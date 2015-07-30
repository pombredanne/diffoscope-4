# -*- coding: utf-8 -*-
#
# diffoscope: in-depth comparison of files, archives, and directories
#
# Copyright © 2014-2015 Jérémy Bobbio <lunar@debian.org>
#           ©      2015  Helmut Grohne <helmut@subdivi.de>
#
# diffoscope is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# diffoscope is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with diffoscope.  If not, see <http://www.gnu.org/licenses/>.

from itertools import dropwhile, starmap
import magic
#import multiprocessing
import multiprocessing.dummy as multiprocessing
import operator
import os.path
import re
import signal
import subprocess
import sys
import tlsh
import diffoscope
from diffoscope import logger, tool_required
from diffoscope.config import Config
from diffoscope.difference import Difference
from diffoscope.comparators.binary import \
    File, FilesystemFile, NonExistingFile, compare_binary_files
from diffoscope.comparators.bzip2 import Bzip2File
from diffoscope.comparators.java import ClassFile
from diffoscope.comparators.cpio import CpioFile
from diffoscope.comparators.deb import DebFile, Md5sumsFile, DebDataTarFile
from diffoscope.comparators.debian import DotChangesFile
from diffoscope.comparators.device import Device
from diffoscope.comparators.directory import Directory, compare_directories
from diffoscope.comparators.elf import ElfFile, StaticLibFile
from diffoscope.comparators.fonts import TtfFile
from diffoscope.comparators.gettext import MoFile
from diffoscope.comparators.gzip import GzipFile
from diffoscope.comparators.haskell import HiFile
from diffoscope.comparators.ipk import IpkFile
from diffoscope.comparators.iso9660 import Iso9660File
from diffoscope.comparators.mono import MonoExeFile
from diffoscope.comparators.pdf import PdfFile
from diffoscope.comparators.png import PngFile
try:
    from diffoscope.comparators.rpm import RpmFile
except ImportError as ex:
    if ex.message != 'No module named rpm':
        raise
    from diffoscope.comparators.rpm_fallback import RpmFile
from diffoscope.comparators.sqlite import Sqlite3Database
from diffoscope.comparators.squashfs import SquashfsFile
from diffoscope.comparators.symlink import Symlink
from diffoscope.comparators.text import TextFile
from diffoscope.comparators.tar import TarFile
from diffoscope.comparators.xz import XzFile
from diffoscope.comparators.zip import ZipFile


def bail_if_non_existing(*paths):
    if not all(map(os.path.lexists, paths)):
        for path in paths:
            if not os.path.lexists(path):
                sys.stderr.write('%s: %s: No such file or directory\n' % (sys.argv[0], path))
        sys.exit(2)


def compare_root_paths(path1, path2):
    if not Config.general.new_file:
        bail_if_non_existing(path1, path2)
    if os.path.isdir(path1) and os.path.isdir(path2):
        return compare_directories(path1, path2)
    file1 = specialize(FilesystemFile(path1))
    file2 = specialize(FilesystemFile(path2))
    return compare_files(file1, file2)


def compare_files(file1, file2, source=None):
    logger.debug('compare files %s and %s', file1, file2)
    with file1.get_content(), file2.get_content():
        if file1.has_same_content_as(file2):
            logger.debug('same content, skipping')
            return None
        specialize(file1)
        specialize(file2)
        if isinstance(file1, NonExistingFile):
            file1.other_file = file2
        elif isinstance(file2, NonExistingFile):
            file2.other_file = file1
        elif file1.__class__.__name__ != file2.__class__.__name__:
            return file1.compare_bytes(file2, source)
        return file1.compare(file2, source)

def compare_commented_files(file1, file2, comment=None, source=None):
    difference = compare_files(file1, file2, source=source)
    if comment:
        if difference is None:
            difference = Difference(None, my_file.name, other_file.name)
        difference.add_comment(comment)
    return difference


class ComparisonPool(object):
    def __init__(self):
        self._manager = multiprocessing.Manager()
        self._condition = self._manager.Condition()
        self._running = self._manager.Value(int, 0)
        self._pool_size = self._manager.Value(int, Config.general.jobs - 1)

    @property
    def manager(self):
        return self._manager

    def grow(self):
        self._condition.acquire()
        self._pool_size.value = self._pool_size.value + 1
        logger.debug('grow pool, new size %s', self._pool_size.value)
        self._condition.notify()
        self._condition.release()

    def shrink(self):
        self._condition.acquire()
        self._pool_size.value = self._pool_size.value - 1
        logger.debug('shrink pool, new size %s', self._pool_size.value)
        assert self._pool_size.value >= 0
        self._condition.release()

    def task_done(self):
        self._condition.acquire()
        self._running.value = self._running.value - 1
        logger.debug('task_done. running %d/%d', self._running.value, self._pool_size.value)
        assert self._running.value >= 0
        self._condition.notify()
        self._condition.release()

    def run_comparison(self, *args):
        self._condition.acquire()
        logger.debug('run comparison. running %d/%d', self._running.value, self._pool_size.value)
        while self._running.value >= self._pool_size.value:
            logger.debug('comparison waiting')
            self._condition.wait()
        self._running.value = self._running.value + 1
        logger.debug('done waiting. running %d/%d', self._running.value, self._pool_size.value)
        self._condition.release()
        p = multiprocessing.Process(target=compare_for_batch, args=args)
        p.daemon = True
        p.start()


class ComparisonBatch(object):
    def __init__(self, pool):
        self._pool = pool
        self._condition = multiprocessing.Condition()
        self._remaining = multiprocessing.Value('i', 0, lock=False)

    @property
    def pool(self):
        return self._pool

    def process(self, comparisons):
        self._condition.acquire()
        assert self._remaining.value == 0
        self._remaining.value = len(comparisons)
        self._condition.release()
        self._outputs = self._pool.manager.list(map(lambda _: None, comparisons))
        for position, comparison in enumerate(comparisons):
            self._pool.run_comparison(self, position, comparison)
            # Stop processing stuff if we are done
            self._condition.acquire()
            try:
                if self._remaining.value == 0:
                    break
            finally:
                self._condition.release()

    def set_result(self, position, result):
        self._outputs[position] = result
        self._condition.acquire()
        if type(result) is Exception:
            self._remaining.value = 0
        else:
            self._remaining.value = self._remaining.value - 1
        logger.debug('%d now remaining %s', id(self), self._remaining.value)
        self._condition.notify()
        self._condition.release()

    def join(self):
        self._condition.acquire()
        while self._remaining.value > 0:
            logger.debug('%d waiting for remaining %s', id(self), self._remaining.value)
            self._condition.wait()
        self._condition.release()
        logger.debug('%d batch is over', id(self))
        for output in self._outputs:
            if isinstance(output, Exception):
                raise output
        return self._outputs


def compare_for_batch(batch, position, comparison):
    try:
        result = compare_commented_files(*comparison)
    except Exception as ex:
        if isinstance(ex, subprocess.CalledProcessError) and \
           ex.returncode == -signal.SIGINT:
            logger.debug('Caught SIGINT')
        else:
            logger.error('Exception in compare_files!', exc_info=True)
        _, result, _ = sys.exc_info()
    logger.debug('got result %s', result)
    batch.set_result(position, result)
    batch.pool.task_done()


def compare_many_files(comparisons):
    if Config.general.jobs == 1:
        return list(starmap(compare_commented_files, comparisons))
    if not hasattr(compare_many_files, 'pool'):
        compare_many_files.pool = ComparisonPool()
    batch = ComparisonBatch(compare_many_files.pool)
    # We are going to keep one process waiting, so let's give more space
    batch.pool.grow()
    batch.process(comparisons)
    try:
        return batch.join()
    finally:
        # We're done. Take the space back
        logger.debug('compare_many_files done')
        batch.pool.shrink()


# The order matters! They will be tried in turns.
FILE_CLASSES = (
    Directory,
    NonExistingFile,
    Symlink,
    Device,
    DotChangesFile,
    Md5sumsFile,
    DebDataTarFile,
    TextFile,
    Bzip2File,
    CpioFile,
    DebFile,
    ElfFile,
    StaticLibFile,
    Sqlite3Database,
    TtfFile,
    MoFile,
    IpkFile,
    GzipFile,
    HiFile,
    Iso9660File,
    ClassFile,
    MonoExeFile,
    PdfFile,
    PngFile,
    RpmFile,
    SquashfsFile,
    TarFile,
    XzFile,
    ZipFile
    )


def specialize(file):
    for cls in FILE_CLASSES:
        if isinstance(file, cls):
            logger.debug("%s is already specialized", file.name)
            return file
        if cls.recognizes(file):
            logger.debug("Using %s for %s", cls.__name__, file.name)
            new_cls = type(cls.__name__, (cls, type(file)), {})
            file.__class__ = new_cls
            return file
    logger.debug('Unidentified file. Magic says: %s', file.magic_file_type)
    return file


def perform_fuzzy_matching(members1, members2):
    if Config.general.fuzzy_threshold == 0:
        return
    already_compared = set()
    # Perform local copies because they will be modified by consumer
    members1 = dict(members1)
    members2 = dict(members2)
    for name1, file1 in members1.iteritems():
        if file1.is_directory() or not file1.fuzzy_hash:
            continue
        comparisons = []
        for name2, file2 in members2.iteritems():
            if name2 in already_compared or file2.is_directory() or not file2.fuzzy_hash:
                continue
            comparisons.append((tlsh.diff(file1.fuzzy_hash, file2.fuzzy_hash), name2))
        if comparisons:
            comparisons.sort(key=operator.itemgetter(0))
            score, name2 = comparisons[0]
            logger.debug('fuzzy top match %s %s: %d difference score', name1, name2, score)
            if score < Config.general.fuzzy_threshold:
                yield name1, name2, score
                already_compared.add(name2)
