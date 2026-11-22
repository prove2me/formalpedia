-- Prove2me | Definitions.Def_Arm64_ISA_State
-- name    : Arm64_ISA_State
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:03:02.711023+00:00
-- url     : https://prove2.me/theorems/c7addf90-7ce2-4da5-bf65-75ea17f8a041
-- title:
--   Arm64.Trusted.ISA.State — ARM64 Architectural State
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/State.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/State.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/State.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/State.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/State.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Syntax
public import Definitions.Def_Arm64_ISA_Memory

/-!
# ARM64 Architectural State (`Arm64.State`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Programmer-visible AArch64 machine state (`State`), including
  condition flags (`PState`: `n`, `z`, `c`, `v`), 64-bit general-purpose registers
  (`RegFile`), 128-bit SIMD/FP registers (`VRegFile`), execution status
  (`ExecStatus`), nondeterministic oracle (`Oracle`, `Timespec`, `MremapRefusal`,
  `SchedAffinityResult`), recorded signal dispositions
  and alternate signal stack (`SigAction`, `SigAltStack`), and state accessors (`readReg64`, `writeReg64`,
  `readReg32`, `writeReg32`, `readVReg128`, `writeVReg128`, `advancePC`, `setPC`).
- **When to read**: Read when writing or auditing `State` field projections in `Spec.lean`
  or checking register/flag/oracle representations; use `ProofLib/State.lean` for rewrite lemmas.
-/

@[expose] public section

namespace Arm64

/-- Processor condition flags (`N`, `Z`, `C`, `V`). -/
@[ext]
structure PState where
  n : Bool := false
  z : Bool := false
  c : Bool := false
  v : Bool := false
  deriving DecidableEq, Repr, Inhabited, BEq

namespace PState

/-- All condition flags clear (`NZCV = 0b0000`). -/
def zero : PState := { n := false, z := false, c := false, v := false }

/-- Construct `PState` from a 4-bit `nzcv` immediate (`N=bit 3, Z=bit 2, C=bit 1, V=bit 0`). -/
def ofBits4 (b : BitVec 4) : PState :=
  { n := b.getLsbD 3
    z := b.getLsbD 2
    c := b.getLsbD 1
    v := b.getLsbD 0 }

end PState

/-- General-purpose register file (`X0..X30`, indexed by `BitVec 5`). -/
@[ext]
structure RegFile where
  regs : BitVec 5 → BitVec 64

namespace RegFile

/-- The default `RegFile` holds zero in every register. -/
instance : Inhabited RegFile := ⟨{ regs := fun _ => 0#64 }⟩

/-- The all-zero general-purpose register file. -/
def empty : RegFile := { regs := fun _ => 0#64 }

/-- Read general-purpose register `idx`. Note this is the raw indexed read; `XZR`/`SP`
    disambiguation happens in `State.readReg64`. -/
def read (rf : RegFile) (idx : BitVec 5) : BitVec 64 :=
  rf.regs idx

/-- Write general-purpose register `idx`. Note this is the raw indexed write; `XZR`/`SP`
    disambiguation happens in `State.writeReg64`. -/
def write (rf : RegFile) (idx : BitVec 5) (val : BitVec 64) : RegFile :=
  { regs := fun i => if i = idx then val else rf.regs i }

end RegFile

/-- 128-bit SIMD/FP register file (`V0..V31` / `Q0..Q31` / `D0..D31` / `S0..S31` / `H0..H31` / `B0..B31`, indexed by `BitVec 5`). -/
@[ext]
structure VRegFile where
  regs : BitVec 5 → BitVec 128

namespace VRegFile

/-- The default `VRegFile` holds zero in every SIMD/FP register. -/
instance : Inhabited VRegFile := ⟨{ regs := fun _ => 0#128 }⟩

/-- The all-zero SIMD/FP register file. -/
def empty : VRegFile := { regs := fun _ => 0#128 }

/-- Read the full 128 bits of SIMD/FP register `idx`. -/
def read (vf : VRegFile) (idx : BitVec 5) : BitVec 128 :=
  vf.regs idx

/-- Write the full 128 bits of SIMD/FP register `idx`. -/
def write (vf : VRegFile) (idx : BitVec 5) (val : BitVec 128) : VRegFile :=
  { regs := fun i => if i = idx then val else vf.regs i }

end VRegFile

/-- Output stream destination for byte-granular write events (`stdout` = fd 1, `stderr` = fd 2,
    or an arbitrary file descriptor `fd`). -/
inductive OutputStream where
  | stdout
  | stderr
  | fd (num : BitVec 64)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace OutputStream

/-- Map a Linux file descriptor (`1` = `stdout`, `2` = `stderr`) to its `OutputStream`. -/
def ofFd (fd : BitVec 64) : OutputStream :=
  if fd == 1#64 then .stdout
  else if fd == 2#64 then .stderr
  else .fd fd

end OutputStream

/-- Observable event in the execution trace. -/
inductive TraceEvent where
  /-- A byte written by the `write` system call (byte granularity). -/
  | writeByte (stream : OutputStream) (byte : BitVec 8)
  /-- An event defined by a user of the semantics. The semantics never produces it; it is for
      externs (`Program.externs`) to record observable effects that the semantics does not model
      (e.g. bytes received from the network, or random bytes generated). -/
  | userDefined (tag : String) (payload : List (BitVec 8))
  /-- `openat` changed the contents of regular file `path` without writing bytes: it created the
      missing file (`O_CREAT`) or truncated an existing one (`O_TRUNC`, also when it was already
      empty). Not output (`traceStreamBytes` drops it). With the `writeByte (.fd _)` events of
      `write`, it is an event of every system call that changes `FsState.files`, so a trace
      segment without either event tells that the system calls left the files alone. -/
  | fileChanged (path : String)
  deriving DecidableEq, Repr, Inhabited, BEq

namespace TraceEvent

/-- Single-byte write event to `stdout` (`fd = 1`). -/
def stdout (byte : BitVec 8) : TraceEvent := .writeByte .stdout byte

/-- Single-byte write event to `stderr` (`fd = 2`). -/
def stderr (byte : BitVec 8) : TraceEvent := .writeByte .stderr byte

/-- Convert a sequence of bytes written to `stream` into byte-granular `TraceEvent`s. -/
def ofBytes (stream : OutputStream) (bytes : List (BitVec 8)) : List TraceEvent :=
  bytes.map (.writeByte stream)

end TraceEvent

/-- Execution status of the machine state. -/
inductive ExecStatus where
  | Running
  | Halted
  | Exited (code : BitVec 64)
  /-- Fatal signal termination (for example `tkill`/`tgkill` delivering `SIGABRT = 6` to the
      calling thread in `abort()`). A POSIX parent shell or `qemu-aarch64` observes wait status
      `128 + sig.toNat` (`134` for `SIGABRT = 6`). -/
  | Signaled (sig : BitVec 7)
  /-- A Rust panic entry point was reached (see `Arm64.Rust.panicExterns`). With
      `panic = abort` a panic never returns, so it ends execution like `exit`. -/
  | Panicked
  /-- A virtual-memory or physical-memory exhaustion condition occurred in `brk`, `mmap`,
      `mprotect`, or `mremap` (either no free 48-bit user virtual-address gap of the requested
      size exists in `mmap`, or the net new `Perm.rw` bytes required exceed `State.physMemAvail`).
      Ends execution like `exit` or `panic`. -/
  | OutOfMemory
  | Exception (msg : String)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Per-call result of a Linux AArch64 `clock_gettime` syscall (`struct __kernel_timespec` in
    `include/uapi/linux/time_types.h`, written by `put_timespec64` in `kernel/time/time.c`).

    **Per-call invariants guaranteed by the Linux kernel across all modeled clock IDs `0..7`**
    (`CLOCK_REALTIME = 0`, `CLOCK_MONOTONIC = 1`, `CLOCK_PROCESS_CPUTIME_ID = 2`,
    `CLOCK_THREAD_CPUTIME_ID = 3`, `CLOCK_MONOTONIC_RAW = 4`, `CLOCK_REALTIME_COARSE = 5`,
    `CLOCK_MONOTONIC_COARSE = 6`, `CLOCK_BOOTTIME = 7` in `kernel/time/posix-timers.c` and
    `lib/vdso/gettimeofday.c`):
    - **Normalized nanoseconds (`0 ≤ tv_nsec < 1_000_000_000`, enforced by `Fin 1000000000`)**:
      high-resolution getters (`ktime_get_real_ts64`, `ktime_get_ts64`, `ktime_get_raw_ts64` in
      `kernel/time/timekeeping.c` and vDSO `do_hres` in `lib/vdso/gettimeofday.c`) reduce
      nanoseconds via `__iter_div_u64_rem(..., NSEC_PER_SEC, &ns)`; coarse getters
      (`ktime_get_coarse_real_ts64`, `ktime_get_coarse_ts64` and vDSO `do_coarse`) and
      time-namespace offset additions (`timens_add_monotonic`, `timens_add_boottime` in
      `include/linux/time_namespace.h`) normalize via `set_normalized_timespec64`
      (`kernel/time/time.c`), which adjusts `tv_sec` in both loops `while (nsec >= NSEC_PER_SEC)`
      and `while (nsec < 0)` so `0 ≤ tv_nsec < 1_000_000_000` even when `tv_sec < 0`; and
      `CLOCK_BOOTTIME` (`ktime_get_boottime_ts64`) and CPU clocks (`posix_cpu_clock_get` in
      `kernel/time/posix-cpu-timers.c`) convert `s64` nanoseconds via `ns_to_timespec64`
      (`kernel/time/time.c`), which likewise guarantees `0 ≤ tv_nsec < 1_000_000_000`.
    - **Seconds (`sec : BitVec 64`, unconstrained)**:
      `CLOCK_REALTIME` (`0`) and `CLOCK_REALTIME_COARSE` (`5`) cannot be set before the 1970 epoch
      (`timespec64_valid` in `include/linux/time64.h` rejects `ts->tv_sec < 0`, and
      `timespec64_valid_settod` is enforced by `do_settimeofday64`, `timekeeping_inject_offset`,
      and `timekeeping_init` in `kernel/time/timekeeping.c`, as well as `do_sys_settimeofday64` in
      `kernel/time/posix-stubs.c`). In the initial time namespace (`init_time_ns`), all eight
      clocks `0..7` satisfy `tv_sec ≥ 0`. However, under `CONFIG_TIME_NS` (`CLONE_NEWTIME`),
      `proc_timens_set_offset` (`kernel/time/namespace.c`) validates a negative `CLOCK_MONOTONIC`
      offset against high-resolution `ktime_get_ts64` (`tp.tv_sec ≥ 0`), whereas
      `posix_get_monotonic_coarse` (`CLOCK_MONOTONIC_COARSE = 6`) and `posix_get_monotonic_raw`
      (`CLOCK_MONOTONIC_RAW = 4`) apply that same `ns->offsets.monotonic` via
      `timens_add_monotonic` (`kernel/time/posix-timers.c`, `lib/vdso/gettimeofday.c`): because
      `ktime_get_coarse_ts64` omits the sub-tick `timekeeping_get_ns(&tk->tkr_mono)` delta and
      `ktime_get_raw_ts64` omits NTP slewing, `timens_add_monotonic` can normalize `tv_sec` to a
      negative value (e.g. `-1`) while keeping `0 ≤ tv_nsec < 1_000_000_000`. Moreover, even for
      single calls, `CLOCK_REALTIME` can jump backward across calls (`clock_settime` / `adjtimex`).
      Leaving `sec : BitVec 64` unconstrained with `nsec : Fin 1000000000` therefore captures the
      exact per-call invariant guaranteed across all clocks `0..7`. -/
structure Timespec where
  sec  : BitVec 64 := 0#64
  nsec : Fin 1000000000 := ⟨0, Nat.zero_lt_succ _⟩
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Non-deterministic refusal outcome for a valid `mremap` call (`Oracle.mremapRefusal`,
    over-approximating host limits and VMA boundaries invisible in flat byte-granular `Memory`):
    - `enomem`: returns `-ENOMEM` (`12`, e.g. `RLIMIT_AS` in `may_expand_vm` or
      `vm.max_map_count` in `check_map_count_against_split_early`, `mm/mremap.c:1870,2039`);
    - `efault`: returns `-EFAULT` (`14`, e.g. `old_len > vma->vm_end - addr` in
      `check_prep_vma`, `mm/mremap.c:1849`, when adjacent anonymous mappings remain separate
      `vm_area_struct`s in the kernel maple tree). -/
inductive MremapRefusal where
  | enomem
  | efault
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Per-call kernel environment for `sched_getaffinity` (`Oracle.schedGetaffinity`,
    `kernel/sched/syscalls.c:1278-1333`):
    - `singleCpu0`: single-CPU kernel (`nr_cpu_ids = 1`, `cpumask_size() = 8`) with CPU 0 online;
    - `hostMask nrCpuIds maskWords`: multi-CPU kernel with `nr_cpu_ids = max 1 (min 8192 nrCpuIds)`
      (`cpumask_size() = ((nr_cpu_ids + 63) / 64) * 8` bytes) and 64-bit active-CPU mask words
      `maskWords` (masked to `[0, nr_cpu_ids)`, defaulting bit 0 to `1` if empty);
    - `refuseEnomem`: `zalloc_cpumask_var` allocation failure (`-ENOMEM`);
    - `refuseEperm`: LSM `security_task_getscheduler` refusal (`-EPERM`). -/
inductive SchedAffinityResult where
  | singleCpu0
  | hostMask (nrCpuIds : Nat) (maskWords : List (BitVec 64))
  | refuseEnomem
  | refuseEperm
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Results of the nondeterministic system calls. Query `n` is the `n`-th nondeterministic
    syscall of the run, counting from zero (`State.oracleIdx`).

    `Step` stays deterministic. The nondeterminism comes from the initial state: specs such as
    `subroutine_ok` quantify over every entry state `s0`, so they hold for every `s0.oracle`,
    i.e. for every possible kernel behaviour. Indexing by the query count loses nothing:
    given `s0`, the whole history before query `n` is determined, so a kernel that looks at
    that history (including the clock ID passed to `clock_gettime`) is still just some function
    of `n`.

    - `mmap n`: preferred address candidate for the `n`-th query if it is an anonymous `mmap`
      or `mremap(..., MREMAP_MAYMOVE)`. `execMmap` and `execMremap` sanitize the candidate
      (`mm/mmap.c` `get_unmapped_area`): if it is below `MMAP_MIN_ADDR`, not page-aligned,
      exceeds the 48-bit user virtual address space (`2 ^ 48`), or overlaps an already-mapped
      byte, they deterministically substitute the lowest free page-aligned gap in
      `[MMAP_MIN_ADDR, 2 ^ 48)` that fits, failing only when no free gap of the requested size
      exists,
    - `mremapRefusal n`: optional non-deterministic refusal (`some .enomem` -> `-ENOMEM` for
      `RLIMIT_AS` / `vm.max_map_count`, or `some .efault` -> `-EFAULT` when `[oldAddr, oldAddr + oldLen)`
      spans unmerged adjacent VMAs in `check_prep_vma`, leaving existing mappings intact),
    - `schedGetaffinity n`: kernel `nr_cpu_ids`, active `cpumask_t`, or `-ENOMEM`/`-EPERM` refusal
      observed by the `n`-th query if it is `sched_getaffinity` (defaulting to `.singleCpu0`),
    - `getrandom n i`: byte `i` of the buffer filled by the `n`-th query if it is a `getrandom`,
    - `clockGettime n`: normalized `struct timespec` (`0 ≤ nsec < 1_000_000_000`) written by the
      `n`-th query if it is a successful `clock_gettime`, with no monotonicity relation between
      successive queries,
    - `exclFails`: finite schedule of spurious store-exclusive (`STXR*`/`STLXR*`/`STXP`/`STLXP`)
      failures copied into `State.exclFails` at process load time (`ElfImage.loadState`). Every
      execution has finitely many spurious failures, adversarially placed (`headD false`,
      consumed per non-faulting store-exclusive). This models eventual LL/SC progress without an
      exclusive monitor; a retry-less `stxr` is unprovable because `exclFails = [true]` is a
      valid initial state. -/
structure Oracle where
  mmap             : Nat → BitVec 64 := fun _ => 0#64
  mremapRefusal    : Nat → Option MremapRefusal := fun _ => none
  schedGetaffinity : Nat → SchedAffinityResult := fun _ => .singleCpu0
  getrandom        : Nat → Nat → BitVec 8 := fun _ _ => 0#8
  clockGettime     : Nat → Timespec := fun _ => {}
  exclFails        : List Bool := []

instance : Inhabited Oracle := ⟨{}⟩

/-- Inode payload in the local file system (`file` byte sequence or `dir` directory entry). -/
inductive FsEntry where
  | file (bytes : List (BitVec 8))
  | dir
  deriving DecidableEq, Repr, Inhabited, BEq

/-- File-descriptor access mode (`O_RDONLY`, `O_WRONLY`, `O_RDWR`). -/
inductive FdAccessMode where
  | rdonly
  | wronly
  | rdwr
  deriving DecidableEq, Repr, Inhabited, BEq

namespace FdAccessMode

/-- True when the open file description permits reading (`O_RDONLY` or `O_RDWR`). -/
def canRead : FdAccessMode → Bool
  | .rdonly | .rdwr => true
  | .wronly => false

/-- True when the open file description permits writing (`O_WRONLY` or `O_RDWR`). -/
def canWrite : FdAccessMode → Bool
  | .wronly | .rdwr => true
  | .rdonly => false

end FdAccessMode

/-- Descriptor backend tag for entries in `FsState.fds`:
    - `localFile`: regular file backed by `FsState.files`.
    - `localDir`: read-only directory descriptor (`O_RDONLY`, `S_IFDIR | 0755`) backed by
      `FsState.files` (`fstat` returns `encodeLinuxStat .dir`, `read` returns `-EISDIR`, `write`
      returns `-EBADF`, `close` returns `0`, and `pread64`/`lseek` fail closed).
    - `stdio`: standard stream (`stdin` / `stdout` / `stderr`), stored out of band from the
      working-directory file namespace (`FsState.entries`) in `FsState.stdin` / `State.trace`.
    - `custom (tag : Nat)`: extension slot for future loopback socket / pipe / peer-oracle backends
      sharing `FsState.fds` without changing any `FdEntry` field or invalidating file-descriptor proofs. -/
inductive FdKind where
  | localFile
  | localDir
  | stdio
  | custom (tag : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Linux 64-bit `MAX_LFS_FILESIZE` (`include/linux/fs.h`, `LLONG_MAX = 2 ^ 63 - 1`): maximum
    file size and byte offset (`loff_t`) representable in a signed 64-bit file offset. -/
def MAX_LFS_FILESIZE : Nat := 2 ^ 63 - 1

/-- Canonical relative path in the working-directory file-system model (`[]` = `"."`). -/
abbrev FsPath := List String

/-- Split `s` on `'/'` into raw path segments using pure `List Char` recursion so path
    normalization reduces directly in the Lean kernel (`rfl` / `decide +kernel`) across `module`
    boundaries. -/
def splitSlash (s : String) : List String :=
  let rec go (cur : List Char) : List Char → List String
    | [] => [String.ofList cur.reverse]
    | '/' :: cs => String.ofList cur.reverse :: go [] cs
    | c :: cs => go (c :: cur) cs
  go [] s.toList

/-- True when `path` begins with `'/'`. -/
def hasLeadingSlash (path : String) : Bool :=
  path.toList.head? == some '/'

/-- True when `path` contains a `".."` path segment. -/
def hasDotDot (path : String) : Bool :=
  (splitSlash path).contains ".."

/-- Normalize a relative POSIX pathname into its canonical non-empty, non-`"."` path segments
    (`normalizePath "./coins" = ["coins"]`, `normalizePath ".//a/./b/" = ["a", "b"]`,
    `normalizePath "." = []`, `normalizePath "./" = []`). -/
def normalizePath (path : String) : FsPath :=
  (splitSlash path).filter fun seg => !seg.isEmpty && seg != "."

/-- Non-empty path prefixes of `segs` in top-down order
    (`FsPath.nonEmptyPrefixes ["a", "b", "c"] = [["a"], ["a", "b"], ["a", "b", "c"]]`). -/
def FsPath.nonEmptyPrefixes : FsPath → List FsPath
  | [] => []
  | s :: rest => [s] :: (nonEmptyPrefixes rest).map (s :: ·)

/-- Join `List (List Char)` segments with `'/'` using pure `List Char` recursion. -/
def joinSlashChars : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: rest => s ++ ('/' :: joinSlashChars rest)

/-- Canonical `String` form of `p : FsPath` (`[] ↦ "."`, `["a", "b"] ↦ "a/b"`). -/
def FsPath.toPathString : FsPath → String
  | [] => "."
  | segs => String.ofList (joinSlashChars (segs.map String.toList))

/-- Open file description entry in the process file-descriptor table (regular files, read-only
    directories, and standard streams). -/
structure FdEntry where
  path    : String
  accMode : FdAccessMode
  append  : Bool := false
  cloexec : Bool := false
  offset  : Nat  := 0
  kind    : FdKind := .localFile
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Process working-directory file-system tree (`entries`, keyed by canonical `FsPath` relative to
    `AT_FDCWD`, with `[]` denoting `"."`), out-of-band standard input stream bytes (`stdin`), and
    open file-descriptor table (`fd ∈ [3, 1024)` plus standard streams `0, 1, 2`). -/
structure FsState where
  entries : FsPath → Option FsEntry := fun p => if p.isEmpty then some .dir else none
  stdin   : List (BitVec 8) := []
  fds     : BitVec 64 → Option FdEntry := fun _ => none
  deriving Inhabited

namespace FsState

/-- Maximum open file descriptor number + 1 (`RLIMIT_NOFILE = 1024`). -/
def maxOpenFds : Nat := 1024

/-- Look up canonical relative path `p` in `fs`, treating CWD (`[]`) as always `.dir`. -/
def getEntry (fs : FsState) (p : FsPath) : Option FsEntry :=
  if p.isEmpty then some .dir else fs.entries p

/-- Update canonical relative path `p` in `fs.entries`. -/
def setEntry (fs : FsState) (p : FsPath) (e : Option FsEntry) : FsState :=
  { fs with entries := fun q => if q == p then e else fs.entries q }

/-- Look up `path` in `fs` under its canonical `normalizePath` key. -/
def files (fs : FsState) (path : String) : Option FsEntry :=
  fs.getEntry (normalizePath path)

/-- Update `path` in `fs` under its canonical `normalizePath` key (`(fs.setFile "./f" v).files "f" = v` by `rfl`). -/
def setFile (fs : FsState) (path : String) (e : Option FsEntry) : FsState :=
  fs.setEntry (normalizePath path) e

/-- Byte sequence backing an open `.localFile` or `.stdio` descriptor (`fs.stdin` for `.stdio`,
    `fs.files desc.path` regular-file bytes for `.localFile`, `[]` otherwise). -/
def fdBytes (fs : FsState) (desc : FdEntry) : List (BitVec 8) :=
  match desc.kind with
  | .stdio => fs.stdin
  | .localFile => match fs.files desc.path with | some (.file bs) => bs | _ => []
  | .localDir | .custom _ => []

/-- Update descriptor `fd` in `fs.fds`. -/
def setFd (fs : FsState) (fd : BitVec 64) (e : Option FdEntry) : FsState :=
  { fs with fds := fun k => if k == fd then e else fs.fds k }

/-- Allocate the lowest unused file descriptor `fd ∈ [3, maxOpenFds)`. -/
def allocFd (fs : FsState) : Option (BitVec 64) :=
  ((List.range (maxOpenFds - 3)).find? fun i =>
    fs.fds (BitVec.ofNat 64 (i + 3)) == none).map fun i => BitVec.ofNat 64 (i + 3)

end FsState

/-- Modeled `FPSR` mask (`0x0800009f`): cumulative IEEE 754 exception flags
    `IOC` (bit 0), `DZC` (bit 1), `OFC` (bit 2), `UFC` (bit 3), `IXC` (bit 4),
    `IDC` (bit 7), and cumulative SIMD saturation flag `QC` (bit 27).
    All other bits (`[6:5]`, `[26:8]`, and AArch32-only `NZCV` `[31:28]`) are `RES0`. -/
def fpsrMask : BitVec 32 := 0x0800009f#32

/-- `FPSR.IOC` (bit 0): Invalid Operation cumulative exception flag. -/
def fpsrIOC : BitVec 32 := 0x00000001#32

/-- `FPSR.DZC` (bit 1): Divide by Zero cumulative exception flag. -/
def fpsrDZC : BitVec 32 := 0x00000002#32

/-- `FPSR.OFC` (bit 2): Overflow cumulative exception flag. -/
def fpsrOFC : BitVec 32 := 0x00000004#32

/-- `FPSR.UFC` (bit 3): Underflow cumulative exception flag. -/
def fpsrUFC : BitVec 32 := 0x00000008#32

/-- `FPSR.IXC` (bit 4): Inexact cumulative exception flag. -/
def fpsrIXC : BitVec 32 := 0x00000010#32

/-- `FPSR.IDC` (bit 7): Input Denormal cumulative exception flag. -/
def fpsrIDC : BitVec 32 := 0x00000080#32

/-- `FPSR.QC` (bit 27): Cumulative SIMD saturation flag. -/
def fpsrQC : BitVec 32 := 0x08000000#32

/-- Per-signal 32-byte kernel disposition entry (`struct k_sigaction` on AArch64 Linux,
    `include/linux/signal_types.h` and `arch/arm64/include/uapi/asm/signal.h`):
    `handler` (`0` = `SIG_DFL`, `1` = `SIG_IGN`, or a recorded user-space handler address for
    synchronous fault signals `SIGSEGV` / `SIGBUS`), `flags`, `restorer`, and 64-bit `mask`.
    Signal dispositions are recorded and returned by `rt_sigaction`; asynchronous signal
    delivery is not modeled, and hardware faults terminate fail-closed with `.Exception`. -/
structure SigAction where
  handler  : BitVec 64 := 0#64
  flags    : BitVec 64 := 0#64
  restorer : BitVec 64 := 0#64
  mask     : BitVec 64 := 0#64
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Per-thread alternate signal stack configuration (`current->sas_ss_sp`, `current->sas_ss_size`,
    `current->sas_ss_flags` in `include/linux/sched.h`, `include/linux/sched/signal.h:571-615`, and
    `kernel/signal.c:4458`): `sp` (`0` when disabled), `size` (`0` when disabled, reporting
    `SS_DISABLE = 2`), and the raw stored `ssFlags` word (`sas_ss_flags`, written verbatim by
    `do_sigaltstack` in `kernel/signal.c:4508`; its `SS_AUTODISARM = 1 << 31` bit suppresses
    `on_sig_stack`). Alternate-stack settings are recorded and returned by `sigaltstack`; signal
    delivery is not modeled. -/
@[ext]
structure SigAltStack where
  sp      : BitVec 64 := 0#64
  size    : BitVec 64 := 0#64
  ssFlags : BitVec 32 := 0#32
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Complete AArch64 architectural machine state, plus the process state this model keeps
    for Linux syscalls and hardware nondeterminism (`brkStart`, `brk`, `fs`, `oracle`,
    `oracleIdx`, `exclFails`, `trace`, `status`, `sigActions`, `sigAltStack`, `sigMask`,
    `sigPending`). -/
@[ext]
structure State where
  regs      : RegFile := RegFile.empty
  vregs     : VRegFile := VRegFile.empty
  sp        : BitVec 64 := 0#64
  pc        : BitVec 64 := 0#64
  pstate    : PState := PState.zero
  mem       : Memory := Memory.empty
  tpidrEl0  : BitVec 64 := 0#64
  /-- Floating-point status register (`FPSR`), storing sticky IEEE 754 exception flags
      (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, `IDC`) and cumulative SIMD saturation (`QC`). -/
  fpsr      : BitVec 32 := 0#32
  /-- Initial program break (`mm->start_brk`), fixed at load or snapshot time.
      Execution (`Step`) never modifies `brkStart`. -/
  brkStart  : BitVec 64 := 0#64
  brk       : BitVec 64 := 0#64
  /-- Cooperative local-disk file system and open file-descriptor table. -/
  fs        : FsState := {}
  /-- Results of nondeterministic syscalls. Execution never modifies it. -/
  oracle    : Oracle := {}
  /-- Number of `oracle` queries so far, i.e. the index of the next query. -/
  oracleIdx : Nat := 0
  /-- Remaining schedule of spurious store-exclusive (`STXR*`/`STLXR*`/`STXP`/`STLXP`) failures.
      Every execution has finitely many spurious failures, adversarially placed: each
      non-faulting store-exclusive consumes the head (`headD false`), failing (`Ws := 1`,
      memory unchanged) on `true` and succeeding (`Ws := 0`, performing the store) on `false`
      or once `exclFails` is empty. This models eventual LL/SC progress without an exclusive
      monitor; a retry-less `stxr` is unprovable because `exclFails = [true]` is a valid
      initial state. -/
  exclFails : List Bool := []
  trace     : List TraceEvent := []
  status    : ExecStatus := .Running
  /-- Per-object symbol address table: `symtab obj name` is the runtime address of
      symbol `name` in object `obj` (`none` if absent or non-unique). For extern stubs
      and extern data (not owned by any loaded object), pass `""` as `obj` (or any name
      not matching a loaded object).
      Execution (`Step`) never modifies `symtab`. -/
  symtab      : String → String → Option (BitVec 64) := fun _ _ => none
  /-- Per-signal recorded kernel `k_sigaction` table (`1..64`), initialized to `SIG_DFL` (`0`)
      with zero flags, restorer, and mask (`exec_init_sighand` / `flush_signal_handlers` in
      `kernel/signal.c` for default dispositions). -/
  sigActions  : BitVec 32 → SigAction := fun _ => {}
  /-- Per-thread alternate signal stack configuration, initialized to `{}` (`sp = 0`, `size = 0`,
      raw `ssFlags = 0`, reporting `ss_flags = SS_DISABLE = 2` per `sas_ss_flags` in
      `include/linux/sched/signal.h:602-608`; see `E1` in `Arm64/Trusted/Process/Assumptions.lean`
      for why the raw flags are `0` rather than the `sas_ss_reset` value `SS_DISABLE`). -/
  sigAltStack : SigAltStack := {}
  /-- Per-thread blocked signal mask (`current->blocked`, bit `sig - 1` for `1 ≤ sig ≤ 64`),
      initialized to `0` (empty blocked mask; see `E1` in `Arm64/Trusted/Process/Assumptions.lean`).
      `SIGKILL` (`9`) and `SIGSTOP` (`19`) are never blockable (`SIG_UNBLOCKABLE_MASK`). -/
  sigMask     : BitVec 64 := 0#64
  /-- Per-thread pending signal bitset (`bit sig - 1` for `1 ≤ sig ≤ 64`), initialized to `0`
      (empty pending set; see `E1` in `Arm64/Trusted/Process/Assumptions.lean`).
      Queued by `tkill`/`tgkill` when `SIGABRT` is blocked in `sigMask`, flushed by
      `rt_sigaction(SIGABRT, SIG_IGN, ...)` and delivered synchronously when `rt_sigprocmask`
      unblocks it. -/
  sigPending  : BitVec 64 := 0#64
  /-- Remaining dynamic physical `Perm.rw` byte budget (`mm/mmap.c` `accountable_mapping` /
      `__vm_enough_memory`). Initialized from `inputs.init.physMemAvail` in `ElfImage.loadState`
      after ELF `PT_LOAD` segments and the initial stack are mapped; pure ISA steps and I/O
      syscalls leave `physMemAvail` unchanged, while VM syscalls (`brk`, `mmap`, `mprotect`,
      `munmap`, `mremap`) deduct newly mapped/promoted `Perm.rw` bytes and refund unmapped or
      `PROT_NONE`-demoted `Perm.rw` bytes. -/
  physMemAvail : Nat := 0
  deriving Inhabited

namespace State

/-- Address of symbol `name` in object `obj` from `s.symtab` (`0` if absent). -/
def sym (s : State) (obj name : String) : BitVec 64 :=
  (s.symtab obj name).getD 0#64

/-- Read a 128-bit SIMD/FP register (`V0..V31` / `Q0..Q31`). -/
def readVReg128 (s : State) (idx : BitVec 5) : BitVec 128 :=
  s.vregs.read idx

/-- Write a 128-bit SIMD/FP register (`V0..V31` / `Q0..Q31`). -/
def writeVReg128 (s : State) (idx : BitVec 5) (val : BitVec 128) : State :=
  { s with vregs := s.vregs.write idx val }

/-- Read the low 64 bits (`D0..D31`) of SIMD/FP register `idx`. -/
def readVReg64 (s : State) (idx : BitVec 5) : BitVec 64 :=
  (s.readVReg128 idx).truncate 64

/-- Write a 64-bit value (`D0..D31` or 64-bit vector `v.8b`/`v.4h`/`v.2s`/`v.1d`), zero-extending to 128 bits per AArch64 architecture. -/
def writeVReg64 (s : State) (idx : BitVec 5) (val : BitVec 64) : State :=
  s.writeVReg128 idx (val.zeroExtend 128)

/-- Read the low 32 bits (`S0..S31`) of SIMD/FP register `idx`. -/
def readVReg32 (s : State) (idx : BitVec 5) : BitVec 32 :=
  (s.readVReg128 idx).truncate 32

/-- Write a 32-bit value (`S0..S31`), zero-extending to 128 bits per AArch64 architecture. -/
def writeVReg32 (s : State) (idx : BitVec 5) (val : BitVec 32) : State :=
  s.writeVReg128 idx (val.zeroExtend 128)

/-- Read a 64-bit register (`X0..X30`, `SP`, or `XZR`). -/
def readReg64 (s : State) (r : Reg) : BitVec 64 :=
  match r with
  | .gpr idx => if idx == 31#5 then 0#64 else s.regs.read idx
  | .sp      => s.sp
  | .xzr     => 0#64

/-- Write a 64-bit register (`X0..X30`, `SP`, or `XZR`). Writes to `XZR` are ignored. -/
def writeReg64 (s : State) (r : Reg) (val : BitVec 64) : State :=
  { s with
    regs := match r with
      | .gpr idx => if idx == 31#5 then s.regs else s.regs.write idx val
      | _ => s.regs
    sp := match r with
      | .sp => val
      | _ => s.sp }

/-- Read the low 32 bits of a register (`W0..W30`, `WSP`, or `WZR`). -/
def readReg32 (s : State) (r : Reg) : BitVec 32 :=
  (s.readReg64 r).truncate 32

/-- Write a 32-bit value to a register (`W0..W30`, `WSP`, or `WZR`), zero-extending to 64 bits per AArch64 architecture. -/
def writeReg32 (s : State) (r : Reg) (val : BitVec 32) : State :=
  s.writeReg64 r (val.zeroExtend 64)

/-- Read register at width `w` (`W32` zero-extended to 64 bits, or `W64`). -/
def readReg (s : State) (w : Width) (r : Reg) : BitVec 64 :=
  match w with
  | .W32 => (s.readReg32 r).zeroExtend 64
  | .W64 => s.readReg64 r

/-- Write register at width `w` (`W32` truncates to 32 bits and zero-extends to 64 bits; `W64` writes all 64 bits). -/
def writeReg (s : State) (w : Width) (r : Reg) (val : BitVec 64) : State :=
  s.writeReg64 r (match w with | .W32 => (val.truncate 32).zeroExtend 64 | .W64 => val)

/-- Advance `PC` by 4 bytes (`s.pc + 4`). -/
def advancePC (s : State) : State :=
  { s with pc := s.pc + 4#64 }

/-- Set `PC` to `newPC`. -/
def setPC (s : State) (newPC : BitVec 64) : State :=
  { s with pc := newPC }

/-- Update `PState` flags. -/
def setPState (s : State) (ps : PState) : State :=
  { s with pstate := ps }

/-- Set `FPSR` to `fpsr`. -/
def setFpsr (s : State) (fpsr : BitVec 32) : State :=
  { s with fpsr := fpsr }

/-- Accumulate exception or saturation flags into `FPSR` (`s.fpsr ||| flags`). -/
def orFpsr (s : State) (flags : BitVec 32) : State :=
  { s with fpsr := s.fpsr ||| flags }

/-- Update memory. -/
def setMem (s : State) (m : Memory) : State :=
  { s with mem := m }

/-- Update execution status. -/
def setStatus (s : State) (st : ExecStatus) : State :=
  { s with status := st }

/-- Update the program break (`brk`). -/
def setBrk (s : State) (newBrk : BitVec 64) : State :=
  { s with brk := newBrk }

/-- Update the remaining dynamic physical `Perm.rw` byte budget (`physMemAvail`). -/
def setPhysMemAvail (s : State) (n : Nat) : State :=
  { s with physMemAvail := n }

/-- Update the local file system and file-descriptor state (`fs`). -/
def setFs (s : State) (newFs : FsState) : State :=
  { s with fs := newFs }

/-- Read the recorded kernel signal disposition for signal `sig`. -/
def getSigAction (s : State) (sig : BitVec 32) : SigAction :=
  s.sigActions sig

/-- Update the recorded kernel signal disposition for signal `sig`. -/
def setSigAction (s : State) (sig : BitVec 32) (act : SigAction) : State :=
  { s with sigActions := fun k => if k == sig then act else s.sigActions k }

/-- Update the recorded alternate signal stack (`sigAltStack`). -/
def setSigAltStack (s : State) (sas : SigAltStack) : State :=
  { s with sigAltStack := sas }

/-- Update the blocked signal mask (`sigMask`). -/
def setSigMask (s : State) (mask : BitVec 64) : State :=
  { s with sigMask := mask }

/-- Update the pending signal bitset (`sigPending`). -/
def setSigPending (s : State) (pending : BitVec 64) : State :=
  { s with sigPending := pending }

/-- Consume one `oracle` query (increment `oracleIdx`). -/
def nextOracle (s : State) : State :=
  { s with oracleIdx := s.oracleIdx + 1 }

/-- Whether the next non-faulting store-exclusive (`STXR*`/`STLXR*`/`STXP`/`STLXP`) will
    spuriously fail (`s.exclFails.headD false`). Once the finite list `s.exclFails` is
    exhausted, store-exclusives succeed (`false`). -/
def exclWillFail (s : State) : Bool :=
  s.exclFails.headD false

/-- Consume one store-exclusive failure decision (`s.exclFails.tail`). -/
def stepExclOracle (s : State) : State :=
  { s with exclFails := s.exclFails.tail }

/-- Append byte-level events to the observable execution trace (`s.trace ++ evs`). -/
def appendTrace (s : State) (evs : List TraceEvent) : State :=
  { s with trace := s.trace ++ evs }

/-- Extract all bytes written to `stdout` (`fd = 1`) from `s.trace`, in order. -/
def stdoutBytes (s : State) : List (BitVec 8) :=
  s.trace.filterMap fun
    | .writeByte .stdout b => some b
    | _ => none

/-- Extract all bytes written to `stderr` (`fd = 2`) from `s.trace`, in order. -/
def stderrBytes (s : State) : List (BitVec 8) :=
  s.trace.filterMap fun
    | .writeByte .stderr b => some b
    | _ => none

-- ARM Architecture Reference Manual (DDI 0487) HTML links for SP alignment:
-- - Section D1.4.10 ("Program Counter and stack pointer alignment", D1.4.10.2 "SP alignment checking"):
--   https://developer.arm.com/documentation/ddi0487/latest/-Part-D-The-AArch64-System-Level-Architecture/-Chapter-D1-The-AArch64-System-Level-Programmers--Model/-D1-4-Exceptions/-D1-4-10-Program-Counter-and-stack-pointer-alignment
-- - Section C6.1.3 ("Use of the stack pointer"):
--   https://developer.arm.com/documentation/ddi0487/latest/-Part-C-The-AArch64-Instruction-Set/-Chapter-C6-A64-Base-Instruction-Descriptions/-C6-1-About-the-A64-base-instructions/-C6-1-3-Use-of-the-stack-pointer
-- - Section J1.2.305 (`CheckSPAlignment` pseudocode):
--   https://developer.arm.com/documentation/ddi0487/latest/-Part-J-Architectural-Pseudocode/-Chapter-J1-A-profile-Architecture-Pseudocode/-J1-2-Pseudocode-for-AArch64-operation/-J1-2-305-CheckSPAlignment
/-- Architectural stack pointer alignment predicate (`CheckSPAlignment()` in ARMv8-A pseudocode):
    whenever `SP` is used as the base register of a memory access, `SP` must be 16-byte aligned
    (`SP[3:0] == 0b0000`).

    Structured ASL: `arm-asl-extract query CheckSPAlignment` (`shared_pseudocode.xml`, see
    `.agents/skills/review-arm64-asl/SKILL.md`).

    See the ARM Architecture Reference Manual (DDI 0487):
    - [Section D1.4.10: Program Counter and stack pointer alignment](https://developer.arm.com/documentation/ddi0487/latest/%2DPart-D-The-AArch64-System-Level-Architecture/%2DChapter-D1-The-AArch64-System-Level-Programmers--Model/%2DD1-4-Exceptions/%2DD1-4-10-Program-Counter-and-stack-pointer-alignment)
    - [Section C6.1.3: Use of the stack pointer](https://developer.arm.com/documentation/ddi0487/latest/%2DPart-C-The-AArch64-Instruction-Set/%2DChapter-C6-A64-Base-Instruction-Descriptions/%2DC6-1-About-the-A64-base-instructions/%2DC6-1-3-Use-of-the-stack-pointer)
    - [Section J1.2.305: `CheckSPAlignment` pseudocode](https://developer.arm.com/documentation/ddi0487/latest/%2DPart-J-Architectural-Pseudocode/%2DChapter-J1-A-profile-Architecture-Pseudocode/%2DJ1-2-Pseudocode-for-AArch64-operation/%2DJ1-2-305-CheckSPAlignment) -/
@[inline] def spAligned (s : State) : Bool :=
  (s.sp &&& 0b1111#64) == 0#64

end State

end Arm64


