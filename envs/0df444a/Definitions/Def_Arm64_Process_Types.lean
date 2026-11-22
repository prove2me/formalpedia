-- Prove2me | Definitions.Def_Arm64_Process_Types
-- name    : Arm64_Process_Types
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:16:58.22353+00:00
-- url     : https://prove2.me/theorems/a5760e11-22ea-44ea-bd89-5b679b1fce30
-- title:
--   Arm64.Trusted.Process.Types — ELF Process Types
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/Types.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Types.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/Types.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Types.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/Types.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_ISA_Semantics
public import Definitions.Def_Arm64_Object_Reloc

/-!
# ELF Process Types (`Arm64.Trusted.Process.Types`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Contiguous mapped byte regions (`Snapshot.Region`, `Snapshot.cellAt`),
  process-level environment inputs (`AuxvTag`, `AuxvConfig`, `ProcessInit`, `ProcessInputs`), parsed
  static ELF64 image (`ElfImage`), and observable process termination outcome (`ProcessOutcome`).
- **When to read**: Read when writing or auditing whole-binary process specifications
  (`ElfRunsTo`, `ElfCorrect`, `ElfSafe`) or inspecting how `argv`, `envp`, `stdin`, initial files, and
  kernel/environment initialization choices (`init : ProcessInit`) are supplied to an ELF process.
-/

@[expose] public section

namespace Arm64

/-- One contiguous mapped byte region: `bytes` at `[start, start + bytes.length)`, all with `perm`.
    The prefix `[start, start + nonAnonLen)` (0 by default) is backed by an ELF file mapping
    (`anon := false` in `Snapshot.loadCellAt`, matching Linux `fs/binfmt_elf.c` `elf_map` vs
    anonymous `vm_brk_flags` tail). -/
structure Snapshot.Region where
  start      : BitVec 64
  perm       : Perm
  bytes      : List (BitVec 8)
  nonAnonLen : Nat := 0

/-- The permission and byte at `a` in the first region containing `a`, if any. -/
def Snapshot.cellAt (regions : List Snapshot.Region) (a : BitVec 64) :
    Option (Option Perm × BitVec 8) :=
  regions.findSome? fun r =>
    let i := (a - r.start).toNat
    if h : i < r.bytes.length then some (some r.perm, r.bytes[i]) else none

/-- Process-loader cell lookup: like `Snapshot.cellAt`, clearing `lazyFree := false` and marking
    bytes in the file-backed prefix `i < r.nonAnonLen` with `anon := false`. -/
def Snapshot.loadCellAt (regions : List Snapshot.Region) (a : BitVec 64) :
    Option (Option Perm × BitVec 8) :=
  regions.findSome? fun r =>
    let i := (a - r.start).toNat
    if h : i < r.bytes.length then
      let p := { r.perm with lazyFree := false, anon := if i < r.nonAnonLen then false else r.perm.anon }
      some (some p, r.bytes[i])
    else none

end Arm64

namespace Arm64.Process

/-! ## Linux AArch64 Auxiliary Vector Tags (`<elf.h>`) -/

namespace AuxvTag

/-- End of auxiliary vector (`AT_NULL = 0`). -/
def null : BitVec 64 := 0#64
/-- Address of program headers in memory (`AT_PHDR = 3`). -/
def phdr : BitVec 64 := 3#64
/-- Size in bytes of one program header entry (`AT_PHENT = 4`). -/
def phent : BitVec 64 := 4#64
/-- Number of program header entries (`AT_PHNUM = 5`). -/
def phnum : BitVec 64 := 5#64
/-- System page size in bytes (`AT_PAGESZ = 6`, 4096 on AArch64). -/
def pagesz : BitVec 64 := 6#64
/-- Base address of interpreter (`AT_BASE = 7`, 0 for static binaries). -/
def base : BitVec 64 := 7#64
/-- Flags (`AT_FLAGS = 8`, 0). -/
def flags : BitVec 64 := 8#64
/-- Entry point of executable (`AT_ENTRY = 9`). -/
def entry : BitVec 64 := 9#64
/-- Real user ID (`AT_UID = 11`). -/
def uid : BitVec 64 := 11#64
/-- Effective user ID (`AT_EUID = 12`). -/
def euid : BitVec 64 := 12#64
/-- Real group ID (`AT_GID = 13`). -/
def gid : BitVec 64 := 13#64
/-- Effective group ID (`AT_EGID = 14`). -/
def egid : BitVec 64 := 14#64
/-- Address of platform string `"aarch64\0"` (`AT_PLATFORM = 15`). -/
def platform : BitVec 64 := 15#64
/-- CPU feature bitmask (`AT_HWCAP = 16`). -/
def hwcap : BitVec 64 := 16#64
/-- Frequency of `times()` (`AT_CLKTCK = 17`, 100 Hz). -/
def clktck : BitVec 64 := 17#64
/-- Boolean secure-execution mode flag (`AT_SECURE = 23`, 0 for normal execution). -/
def secure : BitVec 64 := 23#64
/-- Address of 16 bytes of random seed data (`AT_RANDOM = 25`). -/
def random : BitVec 64 := 25#64
/-- Extended CPU feature bitmask (`AT_HWCAP2 = 26`). -/
def hwcap2 : BitVec 64 := 26#64
/-- Address of filename string executed (`AT_EXECFN = 31`). -/
def execfn : BitVec 64 := 31#64

end AuxvTag

/-! ## Process Environment Inputs (`AuxvConfig`, `ProcessInit`, `ProcessInputs`) -/

/-- Convert an ASCII `String` into `List (BitVec 8)` (kernel-reducible via `String.toList`). -/
def bytesOfString (s : String) : List (BitVec 8) :=
  s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- Deterministic auxiliary-vector parameters (no ASLR). Image-derived entries (`AT_PHDR`,
    `AT_PHENT`, `AT_PHNUM`, `AT_PAGESZ`, `AT_BASE`, `AT_ENTRY`, `AT_PLATFORM`, `AT_RANDOM`,
    `AT_EXECFN`, `AT_NULL`) are populated automatically by the ELF loader from `ElfImage` and
    the stack layout. -/
structure AuxvConfig where
  /-- 16 deterministic seed bytes placed at the `AT_RANDOM` stack pointer. -/
  randomBytes : List (BitVec 8) := List.replicate 16 0#8
  /-- `AT_HWCAP` feature bitmap (default `0x3 = HWCAP_FP | HWCAP_ASIMD` target-CPU baseline from
      `ID_AA64PFR0_EL1.FP/AdvSIMD ≠ 0xF`, matching the ISA model executing FP/SIMD instructions
      unconditionally; `arch/arm64/include/uapi/asm/hwcap.h`, `arch/arm64/kernel/cpufeature.c`). -/
  hwcap       : BitVec 64 := 0x3#64
  /-- `AT_HWCAP2` extended feature bitmap. -/
  hwcap2      : BitVec 64 := 0#64
  /-- `AT_UID`, `AT_EUID`, `AT_GID`, `AT_EGID` (default `1000`, non-setuid execution). -/
  uid         : BitVec 64 := 1000#64
  euid        : BitVec 64 := 1000#64
  gid         : BitVec 64 := 1000#64
  egid        : BitVec 64 := 1000#64
  /-- `AT_SECURE` secure-execution flag (`0` for normal non-elevated execution;
      `security/commoncap.c` `cap_bprm_creds_from_file`, `fs/binfmt_elf.c` `create_elf_tables`). -/
  secure      : BitVec 64 := 0#64
  /-- Additional `(a_type, a_val)` pairs appended before `AT_NULL`. -/
  extra       : List (BitVec 64 × BitVec 64) := []
  deriving DecidableEq, Repr, Inhabited

/-- Default exclusive upper bound (`vma->vm_end` in Linux `fs/exec.c` `setup_arg_pages`) of the
    initial user stack VMA `[stackTop - stackSize, stackTop)` (`0x0000_7fff_ffff_0000`,
    page-aligned, sitting above the `[sp, stackTop)` `execve` entry image, below the canonical
    user limit, and separate from fixed `ET_EXEC` load addresses). -/
def defaultStackTop : BitVec 64 := 0x00007fffffff0000#64

/-- Default user stack mapping size (`8 MiB = 2048` 4 KiB pages; Linux `_STK_LIM` in
    `include/uapi/linux/resource.h`). -/
def defaultStackSize : Nat := 2048 * Obj.pageSize

/-- Default deterministic anonymous `mmap` base (`0x0000_6000_0000_0000`), placed well above
    fixed `ET_EXEC` segments and `brk` heap and well below the user stack. Returning successive
    64 KiB slots allows multiple anonymous `mmap` calls when `inputs.init.oracle` is not overridden. -/
def defaultOracle : Oracle :=
  { mmap := fun n => 0x0000600000000000#64 + BitVec.ofNat 64 (n * (16 * Obj.pageSize)) }

/-- Nondeterministic kernel, hardware, and environment choices made at Linux `execve(2)`
    process-initialization time (`fs/exec.c` `bprm_mm_init` + `setup_arg_pages`,
    `fs/binfmt_elf.c` `load_elf_binary` + `create_elf_tables`, `arch/arm64/include/asm/elf.h`
    `randomize_stack_top`, `mm/vma.c` `acct_stack_growth`):
    - `auxv`: auxiliary-vector seed, credential, and CPU-feature configuration (`AT_RANDOM`
      16-byte buffer, `AT_HWCAP`/`AT_HWCAP2`, `AT_UID`/`AT_EUID`/`AT_GID`/`AT_EGID`,
      `AT_SECURE`, and optional arch tags),
    - `stackTop`: page-aligned exclusive upper bound of the initial user stack VMA
      `[stackTop - stackSize, stackTop)`, corresponding to Linux `vma->vm_end` *above* the
      `[sp, stackTop)` `execve` entry image (`argc`/`argv`/`envp`/`auxv` table, `AT_RANDOM`,
      `"aarch64\0"`, `argv`/`envp`/`execfn` strings, and top sentinel), not the initial `sp`,
    - `stackSize`: byte size of the initial user stack mapping `[stackTop - stackSize, stackTop)`
      (`RLIMIT_STACK` measured downward from `stackTop = vma->vm_end` as in `acct_stack_growth`,
      charging the entire `[sp, stackTop)` `execve` entry image against `stackSize` and leaving
      `[stackTop - stackSize, sp)` zero-mapped below `sp`),
    - `physMemAvail`: available physical RAM budget in bytes (`1 GiB = 2 ^ 30` by default) for
      dynamic writable anonymous mappings (`Perm.rw`) on top of initial `PT_LOAD` segments and
      the mapped user stack `[stackTop - stackSize, stackTop)`,
    - `oracle`: nondeterministic kernel syscall and hardware store-exclusive (`exclFails`)
      oracle copied into `State.oracle` and `State.exclFails` by `ElfImage.loadState`. -/
structure ProcessInit where
  /-- Auxiliary vector configuration (`AT_RANDOM`, `AT_HWCAP`, credentials, extra tags). -/
  auxv         : AuxvConfig := {}
  /-- Page-aligned exclusive upper bound (`vma->vm_end`) of the initial user stack
      `[stackTop - stackSize, stackTop)`, placed *above* the `[sp, stackTop)` `execve` entry
      image (`buildInitialStack`), not at the initial `sp`. -/
  stackTop     : BitVec 64 := defaultStackTop
  /-- Size in bytes of the mapped user stack `[stackTop - stackSize, stackTop)` (`RLIMIT_STACK`
      measured downward from `stackTop = vma->vm_end`, must be a page-aligned size in
      `[STK_LIM, STACK_SIZE_MAX]`); `ElfImage.loadState` charges the `[sp, stackTop)` `execve`
      entry image against `stackSize` and zero-maps `[stackTop - stackSize, sp)` below `sp`. -/
  stackSize    : Nat := defaultStackSize
  /-- Available physical memory budget in bytes (`2 ^ 30 = 1 GiB` by default) for dynamic
      writable (`Perm.rw`) page allocations after `PT_LOAD` segments and the user stack are
      mapped by `ElfImage.loadState`. -/
  physMemAvail : Nat := 2 ^ 30
  /-- Nondeterministic kernel and hardware oracle (`mmap`, `getrandom`, `clock_gettime`,
      and `exclFails` for spurious `STXR*`/`STLXR*`/`STXP`/`STLXP` store-exclusive failures,
      copied into `State.exclFails` by `ElfImage.loadState`). Defaults to `defaultOracle`
      (`exclFails = []`, under which store-exclusives never fail spuriously); whole-binary
      `ElfSafe`/`ElfCorrect` statements that exercise store-exclusive retry loops must quantify
      over `inputs.init.oracle` (or `inputs.init.oracle.exclFails`) rather than leaving it
      at its default. -/
  oracle       : Oracle := defaultOracle
  deriving Inhabited

/-- Complete system inputs to a Linux AArch64 ELF process, separating caller-supplied /
    filesystem inputs from kernel/environment initialization choices (`init : ProcessInit`):
    - User / caller-supplied inputs: command-line arguments (`argv`), environment variables
      (`envp`), executed filename (`execfn` for `AT_EXECFN`), standard input byte stream
      (`stdin`), and initial working-directory filesystem (`files`, `dirs`).
    - Nondeterministic kernel/environment init record (`init : ProcessInit`): auxiliary-vector
      parameters (`init.auxv`), initial stack geometry (`init.stackTop`, `init.stackSize`),
      available physical memory (`init.physMemAvail`), and syscall/hardware oracle
      (`init.oracle`, including `init.oracle.exclFails`). -/
structure ProcessInputs where
  /-- Command-line argument byte strings (`argv[0..argc-1]`, without trailing NULs). -/
  argv   : List (List (BitVec 8)) := [bytesOfString "prog"]
  /-- Environment variable byte strings (`"KEY=VALUE"`, without trailing NULs). -/
  envp   : List (List (BitVec 8)) := []
  /-- Executed filename byte string (`bprm->filename` for `AT_EXECFN`, without trailing NUL). -/
  execfn : List (BitVec 8) := []
  /-- Initial byte contents of file descriptor `0` (`stdin`). -/
  stdin  : List (BitVec 8) := []
  /-- Initial regular files `(path, bytes)` present in `State.fs.files`. -/
  files  : List (String × List (BitVec 8)) := []
  /-- Initial relative directory paths present in `State.fs`. -/
  dirs   : List String := []
  /-- Kernel/hardware/environment process-initialization choices (`auxv`, `stackTop`,
      `stackSize`, `physMemAvail`, `oracle`). -/
  init   : ProcessInit := {}
  deriving Inhabited

namespace ProcessInputs

/-- Reducible forwarding accessor for `i.init.auxv`. -/
abbrev auxv (i : ProcessInputs) : AuxvConfig := i.init.auxv

/-- Reducible forwarding accessor for `i.init.stackTop`. -/
abbrev stackTop (i : ProcessInputs) : BitVec 64 := i.init.stackTop

/-- Reducible forwarding accessor for `i.init.stackSize`. -/
abbrev stackSize (i : ProcessInputs) : Nat := i.init.stackSize

/-- Reducible forwarding accessor for `i.init.physMemAvail`. -/
abbrev physMemAvail (i : ProcessInputs) : Nat := i.init.physMemAvail

/-- Reducible forwarding accessor for `i.init.oracle`. -/
abbrev oracle (i : ProcessInputs) : Oracle := i.init.oracle

/-- Construct `ProcessInputs` from `String` arguments/environment and `stdin` bytes. -/
def ofStrings (argv : List String := ["prog"]) (envp : List String := [])
    (stdin : List (BitVec 8) := [])
    (files : List (String × List (BitVec 8)) := []) : ProcessInputs :=
  { argv := argv.map bytesOfString
    envp := envp.map bytesOfString
    stdin := stdin
    files := files }

end ProcessInputs

/-! ## Parsed Static ELF64 Image (`ElfImage`) -/

/-- A validated, statically linked AArch64 ELF64 executable image (`ET_EXEC`):
    - `entry`: initial program counter (`e_entry`),
    - `phdrVaddr`: virtual address of the ELF program header table in memory (`AT_PHDR`),
    - `phent`: byte size of each program header entry (`e_phentsize = 56`),
    - `phnum`: number of program header entries (`e_phnum`),
    - `segments`: page-aligned, non-overlapping `PT_LOAD` segments in ascending address order,
    - `brkStart`: page-aligned end of the highest `PT_LOAD` segment (`mm->start_brk`),
    - `symbols`: optional `(name, vaddr)` symbol table extracted from the binary. -/
structure ElfImage where
  entry     : BitVec 64
  phdrVaddr : BitVec 64
  phent     : Nat := 56
  phnum     : Nat
  segments  : List Snapshot.Region
  brkStart  : BitVec 64
  symbols   : List (String × BitVec 64) := []
  deriving Inhabited

/-! ## Observable Process Outcome (`ProcessOutcome`) -/

/-- Observable outcome of a terminated process (`SYS_exit`, `SYS_exit_group`, or fatal signal
    `ExecStatus.Signaled sig`):
    - `exitCode`: exit status (`code` for `.Exited code`; `BitVec.ofNat 64 (128 + sig.toNat)` for
      `.Signaled sig`, matching POSIX shell `$?` and `qemu-aarch64` exit code `134` on `SIGABRT`),
    - `signal`: `none` on normal `exit`/`exit_group`, or `some sig.toNat` (`some 6` for `SIGABRT`)
      on fatal signal death so specifications can distinguish `abort()` from `exit(134)`,
    - `stdout`: ordered sequence of bytes written to `fd = 1` (`OutputStream.stdout`),
    - `stderr`: ordered sequence of bytes written to `fd = 2` (`OutputStream.stderr`),
    - `fs`: final file-system state (`State.fs`). -/
structure ProcessOutcome where
  exitCode : BitVec 64
  signal   : Option Nat := none
  stdout   : List (BitVec 8)
  stderr   : List (BitVec 8)
  fs       : FsState
  deriving Inhabited

namespace ProcessOutcome

/-- Extract all bytes written to `stream` from an execution `trace`. -/
def traceStreamBytes (stream : OutputStream) (trace : List TraceEvent) : List (BitVec 8) :=
  trace.filterMap fun ev =>
    match ev with
    | .writeByte s b => if s == stream then some b else none
    | .userDefined _ _ => none
    | .fileChanged _ => none

/-- Project the observable `ProcessOutcome` from a terminated `.Exited code` state `sf`. -/
def ofState (code : BitVec 64) (sf : State) : ProcessOutcome :=
  { exitCode := code
    signal   := none
    stdout   := traceStreamBytes .stdout sf.trace
    stderr   := traceStreamBytes .stderr sf.trace
    fs       := sf.fs }

/-- Project the observable `ProcessOutcome` from a signal-terminated `.Signaled sig` state `sf`,
    reporting shell / `qemu-aarch64` status `128 + sig.toNat` and `signal := some sig.toNat`. -/
def ofSignal (sig : BitVec 7) (sf : State) : ProcessOutcome :=
  { exitCode := BitVec.ofNat 64 (128 + sig.toNat)
    signal   := some sig.toNat
    stdout   := traceStreamBytes .stdout sf.trace
    stderr   := traceStreamBytes .stderr sf.trace
    fs       := sf.fs }

/-- Extract `some ProcessOutcome` if `sf` has terminated via `.Exited` or `.Signaled`, or `none`
    otherwise. -/
def ofTerminated? (sf : State) : Option ProcessOutcome :=
  match sf.status with
  | .Exited code  => some (ofState code sf)
  | .Signaled sig => some (ofSignal sig sf)
  | _             => none

/-- Look up the final byte contents of regular file `path` in `out.fs`. -/
def fileBytes? (out : ProcessOutcome) (path : String) : Option (List (BitVec 8)) :=
  match out.fs.files path with
  | some (.file bs) => some bs
  | _ => none

end ProcessOutcome

end Arm64.Process


