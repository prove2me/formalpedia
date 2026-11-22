-- Prove2me | Definitions.Def_Arm64_Process_Assumptions
-- name    : Arm64_Process_Assumptions
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:17:14.433035+00:00
-- url     : https://prove2.me/theorems/86edfb4d-ce6d-44b8-b321-07316eae5729
-- title:
--   Arm64.Trusted.Process.Assumptions — Shared Linux execve(2) Input Validity
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/Assumptions.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Assumptions.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/Assumptions.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Assumptions.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/Assumptions.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Process_Types
public import Definitions.Def_Arm64_Syscalls_FileIo

/-!
# Shared Linux `execve(2)` Input Validity (`Arm64.Trusted.Process.Assumptions`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Linux-faithful, decidable preconditions on `ProcessInit` and
  `ProcessInputs` (`ArgsValid` `A1`–`A5`, `AuxvValid` `X1`–`X5`, `StackValid` `S1`–`S5`,
  `ProcessInit.Valid` incl. loader environment assumption `E1`, `SegValid`, `InputPathValid`,
  `FsValid` `F1`–`F6`, `ProcessInputs.Valid`) and kernel-reducible boolean mirrors
  (`ArgsValid.check`, `AuxvValid.check`, `StackValid.check`, `ProcessInit.check`, `SegValid.check`,
  `InputPathValid.check`, `FsValid.check`, `ProcessInputs.check`). Every limit constant cites its
  Linux kernel source. Program-specific hypotheses (`stdin` budgets, `argv` shapes, file-size
  budgets, engine-scope argument path bounds) and `Oracle` fields are deliberately excluded.
  Equivalences `ProcessInit.check_iff_valid` and `ProcessInputs.check_iff_valid` and
  loader/filesystem consequences live in `ProofLib.Process`.
- **When to read**: Read when writing or auditing whole-binary process specifications
  (`∀ inputs, inputs.Valid → …`).
-/

@[expose] public section

namespace Arm64.Process

/-! ## 1. Linux Kernel `execve(2)`, Stack, and Filesystem Constants -/

/-- Per-argument / per-environment string byte ceiling including trailing NUL (`131,072 = 32` 4 KiB
    pages; `include/uapi/linux/binfmts.h` `#define MAX_ARG_STRLEN (PAGE_SIZE * 32)`, enforced by
    `valid_arg_len` in `fs/exec.c`). -/
def MAX_ARG_STRLEN : Nat := 32 * Obj.pageSize

/-- Floor of the `execve` argument/environment area (`131,072` bytes;
    `include/uapi/linux/limits.h` `#define ARG_MAX 131072`, used as the lower floor in
    `bprm_stack_limits` in `fs/exec.c`). -/
def ARG_MAX : Nat := 131072

/-- Default user `RLIMIT_STACK` (`8 MiB = 8 * 1024 * 1024`;
    `include/uapi/linux/resource.h` `#define _STK_LIM (8*1024*1024)`). `bprm_stack_limits` in
    `fs/exec.c` caps the `execve` argument/environment area at `_STK_LIM / 4 * 3 = 6 MiB`. -/
def STK_LIM : Nat := 8 * 1024 * 1024

/-- Maximum initial user stack mapping size (`128 MiB = 128 * 1024 * 1024`, i.e. 16× `_STK_LIM`;
    `include/uapi/linux/resource.h` `_STK_LIM`, `fs/binfmt_elf.c` `setup_arg_pages`, and
    systemd/PAM `RLIMIT_STACK` deployment ceilings). Bounding the eagerly mapped initial stack to
    `[STK_LIM, STACK_SIZE_MAX]` rules out pathological `~255.75 TiB` `RLIMIT_STACK` configurations
    that would exhaust the 48-bit user virtual address space at `execve` time. -/
def STACK_SIZE_MAX : Nat := 128 * 1024 * 1024

/-- Canonical 48-bit user virtual-address ceiling on AArch64 (`2 ^ 48 = 256 TiB`;
    `arch/arm64/include/asm/processor.h` `TASK_SIZE_64` under `VA_BITS = 48`). -/
def TASK_SIZE : Nat := 2 ^ 48

/-- Minimum base address `stackTop - stackSize` of the initial user stack (`2 ^ 38 = 256 GiB`).
    On Linux AArch64, `STACK_TOP = TASK_SIZE_64` (`arch/arm64/include/asm/processor.h`) minus at
    most `STACK_RND_MASK << PAGE_SHIFT` (`≤ 1 GiB` ASLR randomization in
    `arch/arm64/include/asm/elf.h` `randomize_stack_top`, or `~2 ^ 47` under `qemu-aarch64`
    user mode); even on 4 KiB-page `VA_BITS = 39` kernels (`TASK_SIZE_64 = 512 GiB`), `STACK_TOP`
    sits near `512 GiB` and standard stack limits keep `stackTop - stackSize ≥ 256 GiB`, well
    above static `ET_EXEC` segments and multi-GiB `brk` heaps.
    Regular-file byte length ceiling `Arm64.MAX_LFS_FILESIZE = 2 ^ 63 - 1` (`include/linux/fs.h`
    `#define MAX_LFS_FILESIZE ((loff_t)LLONG_MAX)`) is exported from `Arm64.Trusted.ISA.State`. -/
def STACK_BASE_MIN : Nat := 2 ^ 38

/-- Effective `execve` argument + environment byte budget computed by `bprm_stack_limits` in
    `fs/exec.c` for `rlim_stack.rlim_cur = stackSize`:
    `max ARG_MAX (min (STK_LIM / 4 * 3) (stackSize / 4))`. -/
def argLimit (stackSize : Nat) : Nat :=
  max ARG_MAX (min (STK_LIM / 4 * 3) (stackSize / 4))

/-- Total bytes charged against `argLimit` by `fs/exec.c` (`copy_string_kernel` for
    `bprm->filename`, `copy_strings` for `argv` and `envp`, plus one 8-byte pointer slot per
    `argv` and `envp` entry in `bprm_stack_limits` / `acct_arg_size`). -/
def argBytes (i : ProcessInputs) : Nat :=
  (i.execfn.length + 1) +
  i.argv.foldl (fun n s => n + (s.length + 1)) 0 +
  i.envp.foldl (fun n s => n + (s.length + 1)) 0 +
  8 * (i.argv.length + i.envp.length)

/-- The 18 fixed non-null `AT_*` auxiliary-vector tags emitted unconditionally by
    `buildInitialStack` (`Arm64/Trusted/Process/Loader.lean`). -/
def AuxvTag.fixedTags : List (BitVec 64) :=
  [ AuxvTag.phdr, AuxvTag.phent, AuxvTag.phnum, AuxvTag.pagesz, AuxvTag.base, AuxvTag.flags
  , AuxvTag.entry, AuxvTag.uid, AuxvTag.euid, AuxvTag.gid, AuxvTag.egid, AuxvTag.platform
  , AuxvTag.hwcap, AuxvTag.clktck, AuxvTag.secure, AuxvTag.random, AuxvTag.hwcap2, AuxvTag.execfn ]

/-! ## 2. Layered Validity Predicates (`ArgsValid`, `AuxvValid`, `StackValid`, `FsValid`) -/

/-- `A1`–`A5`: Linux `execve(2)` invariants on `argv`, `envp`, and `execfn`.
    Note: `MAX_ARG_STRINGS` (`0x7fffffff`, `include/uapi/linux/binfmts.h` and `count` in
    `fs/exec.c`) is implied by `total` (`argc + envc ≤ argLimit / 8 < 2 ^ 20`) and is therefore
    not modeled as a separate field. -/
structure ArgsValid (i : ProcessInputs) : Prop where
  /-- `A1`: `argc ≥ 1` (`fs/exec.c` `do_execveat_common`, commit `dcd46d897adb`). -/
  argc_pos   : i.argv ≠ []
  /-- `A2`: C-string inputs contain no embedded NUL bytes (`fs/exec.c` `copy_strings`, `fs/namei.c`). -/
  no_nul     : (∀ s ∈ i.argv, 0#8 ∉ s) ∧ (∀ s ∈ i.envp, 0#8 ∉ s) ∧ 0#8 ∉ i.execfn
  /-- `A3`: Every `argv` and `envp` string (with NUL) fits within `MAX_ARG_STRLEN` (`valid_arg_len`). -/
  strlen     : ∀ s ∈ i.argv ++ i.envp, s.length + 1 ≤ MAX_ARG_STRLEN
  /-- `A4`: Executed filename (with NUL) fits within `PATH_MAX` (`fs/namei.c` `getname_flags`). -/
  execfn_len : i.execfn.length < PATH_MAX
  /-- `A5`: Total string + pointer bytes fit within `bprm_stack_limits` (`-E2BIG` guard). -/
  total      : argBytes i ≤ argLimit i.init.stackSize

/-- `X1`–`X5`: Linux `create_elf_tables` (`fs/binfmt_elf.c`) and arm64 CPU feature invariants on
    `AuxvConfig`. -/
structure AuxvValid (a : AuxvConfig) : Prop where
  /-- `X1`: `AT_RANDOM` points to exactly 16 random seed bytes (`u_rand_bytes` in `create_elf_tables`). -/
  random16         : a.randomBytes.length = 16
  /-- `X2a`: Normal non-elevated execution (`AT_SECURE = 0`; `security/commoncap.c` `cap_bprm_creds_from_file`). -/
  nonsecure        : a.secure = 0#64
  /-- `X2b`: Non-setugid credentials implied on Linux by `AT_SECURE = 0` (`security/commoncap.c`
      `cap_bprm_creds_from_file` sets `bprm->secureexec = 1` whenever `euid != uid || egid != gid`,
      and musl `src/env/__init_libc.c` checks `AT_UID == AT_EUID && AT_GID == AT_EGID && !AT_SECURE`). -/
  no_setugid       : a.uid = a.euid ∧ a.gid = a.egid
  /-- `X3a`: At most 6 optional/arch auxiliary-vector entries beyond the 18 fixed tags
      (`include/linux/auxvec.h`, `arch/arm64/include/uapi/asm/auxvec.h`). -/
  extra_le         : a.extra.length ≤ 6
  /-- `X3b`: Extra `AT_*` tags are pairwise distinct, disjoint from the 18 fixed tags, and non-null
      (`AT_NULL = 0` appears only as the final terminator in `create_elf_tables`). -/
  extra_fresh      : (a.extra.map Prod.fst).Pairwise (· ≠ ·) ∧
                     ∀ e ∈ a.extra, e.1 ∉ AuxvTag.fixedTags ∧ e.1 ≠ 0#64
  /-- `X3c`: No `AT_SYSINFO_EHDR` (`33`, `include/uapi/linux/auxvec.h`) entry: the model maps no
      `[vdso]` image (README Gap #2), so a vDSO pointer would reference unmapped memory that libc
      (e.g. musl `__vdsosym`) dereferences. Programs therefore take their `svc #0` fallbacks. -/
  no_vdso          : ∀ e ∈ a.extra, e.1 ≠ 33#64
  /-- `X4`: Target-CPU assumption that every supported CPU implements Floating-point and Advanced
      SIMD (`HWCAP_FP | HWCAP_ASIMD = 0x3`, i.e., `ID_AA64PFR0_EL1.FP/AdvSIMD ≠ 0xF` in
      `arch/arm64/kernel/cpufeature.c` and `arch/arm64/include/uapi/asm/hwcap.h`; Linux also
      supports `ARM64_HAS_NO_FPSIMD` CPUs where these bits are clear). This matches the ISA model
      (`Arm64/Trusted/ISA/Eval.lean`), which executes FP/SIMD instructions unconditionally; all
      higher feature bits (e.g. `HWCAP_ATOMICS`) remain unconstrained. -/
  hwcap_fp_asimd   : a.hwcap &&& 0x3#64 = 0x3#64
  /-- `X5`: Hardware signal-frame ceiling on optional `AT_MINSIGSTKSZ` (`51`,
      `include/uapi/linux/auxvec.h:35`): when present in `a.extra`, `e.2.toNat ≤ 524288`
      (`512 KiB`, safely covering `minsigstksz_setup`'s architectural ceiling
      `SIGFRAME_MAXSZ + 32 = 262,176` B in `arch/arm64/kernel/signal.c:182,1710-1726`; no lower
      floor is imposed because dynamic `signal_minsigstksz` on non-SVE or small-VL AArch64 Linux is
      `round_up(sizeof(struct rt_sigframe), 16) + 32 = 4688 + 32 = 4720 < MINSIGSTKSZ = 5120`). -/
  minsigstksz_bound : ∀ e ∈ a.extra, e.1 = 51#64 → e.2.toNat ≤ 524288

/-- `S1`–`S5`: Linux AArch64 user stack geometry (`fs/exec.c` `setup_arg_pages`,
    `fs/binfmt_elf.c` `load_elf_binary`, `mm/vma.c` `acct_stack_growth`,
    `include/uapi/linux/resource.h` `_STK_LIM`, `arch/arm64/include/asm/processor.h`,
    `arch/arm64/include/asm/elf.h`). `init.stackTop` models `vma->vm_end` *above* the populated
    `[sp, stackTop)` `execve` entry image (`argc`/`argv`/`envp`/`auxv` words, `AT_RANDOM`,
    `"aarch64\0"`, `argv`/`envp`/`execfn` strings, and top sentinel), and `init.stackSize` models
    the `RLIMIT_STACK` window `[stackTop - stackSize, stackTop)` measured downward from `vm_end`
    (`vma->vm_end - new_start ≤ rlimit(RLIMIT_STACK)` in `acct_stack_growth`), so `[sp, stackTop)`
    is charged against `stackSize` and `[stackTop - stackSize, sp)` is the zero-mapped stack
    headroom below initial `sp`. -/
structure StackValid (init : ProcessInit) : Prop where
  /-- `S1`: `stackTop` (`vma->vm_end` above `[sp, stackTop)`, `PAGE_ALIGN` in `fs/exec.c`
      `setup_arg_pages`) is 4 KiB page-aligned and at most `TASK_SIZE` (`2 ^ 48`,
      `arch/arm64/include/asm/processor.h` `TASK_SIZE_64`). -/
  top_aligned  : init.stackTop.toNat % Obj.pageSize = 0 ∧ init.stackTop.toNat ≤ TASK_SIZE
  /-- `S2`: `stackSize` is 4 KiB page-aligned and does not underflow `stackTop`. -/
  size_aligned : init.stackSize % Obj.pageSize = 0 ∧ init.stackSize ≤ init.stackTop.toNat
  /-- `S3`: `8 MiB` stack floor (`STK_LIM`, `include/uapi/linux/resource.h` `#define _STK_LIM
      (8*1024*1024)`), ensuring `argLimit init.stackSize ≤ init.stackSize / 4` (`fs/exec.c`
      `bprm_stack_limits`) so that after charging the `[sp, stackTop)` `execve` entry image
      against `[stackTop - stackSize, stackTop)` (`mm/vma.c` `acct_stack_growth`), nearly `6 MiB`
      (`> 5.99 MiB`) of `[stackTop - stackSize, sp)` stack headroom remains below initial `sp`. -/
  size_floor   : STK_LIM ≤ init.stackSize
  /-- `S4`: `128 MiB` stack ceiling (`STACK_SIZE_MAX = 16 * STK_LIM`; `fs/exec.c`
      `setup_arg_pages` `rlim_stack` cap), ensuring the eagerly mapped initial user stack does
      not consume the user virtual address space. -/
  size_ceil    : init.stackSize ≤ STACK_SIZE_MAX
  /-- `S5`: Stack base `stackTop - stackSize` sits in upper user VA space (`≥ STACK_BASE_MIN =
      256 GiB`; `arch/arm64/include/asm/elf.h` `STACK_TOP` / `randomize_stack_top`). -/
  base_floor   : STACK_BASE_MIN ≤ init.stackTop.toNat - init.stackSize

/-- Shared trusted Linux-validity predicate on process-initialization choices `init : ProcessInit`
    (`AuxvValid init.auxv ∧ StackValid init`; `init.oracle` is intentionally unconstrained).
    - `E1` (post-`execve` inherited signal state in `ElfImage.loadState`): Linux `execve` resets
      caught signal handlers to `SIG_DFL` (`flush_signal_handlers` in `fs/exec.c:1303`,
      `kernel/signal.c:526`) and zeroes `sas_ss_sp` and `sas_ss_size` (`fs/exec.c:1260`), but
      preserves parent `SIG_IGN` dispositions, the parent's raw `sas_ss_flags` word (inherited
      verbatim across `fork`, which calls `sas_ss_reset` only for `CLONE_VM` threads in
      `kernel/fork.c:2381-2382`), the blocked signal mask (`current->blocked`), and any pending
      signals (`pending`). `ElfImage.loadState` models standard un-ignored, unblocked parent
      signal state by initializing `sigActions := fun _ => {}` (`SIG_DFL`, no inherited `SIG_IGN`),
      `sigAltStack := {}` (raw `sas_ss_flags = 0`, as for a process tree that never set an
      alternate stack or last set one with `ss_flags = 0`; `sigaltstack` queries report
      `ss_flags = SS_DISABLE = 2` via `sas_ss_flags` in `include/linux/sched/signal.h:602-608`
      since `sas_ss_size = 0`), `sigMask := 0#64` (empty blocked mask), and `sigPending := 0#64`
      (empty pending set). Both the raw alternate-stack flags and the inherited blocked mask are
      observable (`sigaltstack(&{0, 0, 0}, _)` takes the unchanged-settings early return in
      `do_sigaltstack` at `kernel/signal.c:4486-4493` rather than returning `-ENOMEM`, and
      `rt_sigprocmask(SIG_BLOCK, NULL, &old, 8)` reads back `sigMask`). -/
def ProcessInit.Valid (init : ProcessInit) : Prop :=
  AuxvValid init.auxv ∧ StackValid init

/-- One canonical POSIX pathname segment: non-empty, neither `"."` nor `".."`, containing only
    non-NUL single-byte characters (`< 256`, matching `readCString`) without `'/'`, and at most
    `Arm64.NAME_MAX = 255` characters (`include/uapi/linux/limits.h`, exported from
    `Arm64.Trusted.Syscalls.Fs.Open`). -/
def SegValid (seg : String) : Prop :=
  seg ≠ "" ∧ seg ≠ "." ∧ seg ≠ ".." ∧
  (∀ c ∈ seg.toList, c ≠ '/' ∧ c.toNat ≠ 0 ∧ c.toNat < 256) ∧
  seg.length ≤ NAME_MAX

/-- An initial `dirs`/`files` path is relative, non-empty, and canonical (`normalizePath p = splitSlash p`). -/
def InputPathValid (p : String) : Prop :=
  hasLeadingSlash p = false ∧ splitSlash p ≠ [] ∧ ∀ seg ∈ splitSlash p, SegValid seg

/-- `F1`–`F6`: Consistency invariant on initial working-directory tree inputs (`dirs`, `files`),
    ensuring `initFsState` represents a well-formed POSIX directory tree. -/
structure FsValid (i : ProcessInputs) : Prop where
  /-- `F1`–`F2`: Every `dirs` and `files` key is relative, canonical, and componentwise valid. -/
  paths     : (∀ d ∈ i.dirs, InputPathValid d) ∧ (∀ f ∈ i.files, InputPathValid f.1)
  /-- `F3`: Normalised regular-file paths are pairwise distinct. -/
  nodup     : (i.files.map (fun f => normalizePath f.1)).Pairwise (· ≠ ·)
  /-- `F4`: Every regular file has byte length at most `MAX_LFS_FILESIZE` (`2 ^ 63 - 1`). -/
  file_size : ∀ f ∈ i.files, f.2.length ≤ MAX_LFS_FILESIZE
  /-- `F5`: No regular file path is equal to or a prefix of any directory path. -/
  no_clash  : ∀ f ∈ i.files, ∀ d ∈ i.dirs, ¬ (normalizePath f.1 <+: normalizePath d)
  /-- `F6`: No regular file path is a strict prefix of another regular file path. -/
  no_nest   : ∀ f ∈ i.files, ∀ g ∈ i.files,
                normalizePath f.1 <+: normalizePath g.1 → normalizePath f.1 = normalizePath g.1

/-- Shared trusted Linux-validity predicate on `execve(2)` `ProcessInputs`.
    `stdin` and `init.oracle` are intentionally unconstrained. -/
def ProcessInputs.Valid (i : ProcessInputs) : Prop :=
  ArgsValid i ∧ i.init.Valid ∧ FsValid i

/-! ## 3. Boolean Mirrors (`*.check`) & Kernel `Decidable` Instances -/

/-- Recursive boolean pairwise check matching `List.Pairwise (· ≠ ·)`. -/
def nodupCheck {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => (!xs.contains x) && nodupCheck xs

/-- Boolean mirror of `ArgsValid`. -/
def ArgsValid.check (i : ProcessInputs) : Bool :=
  !i.argv.isEmpty &&
  i.argv.all (fun s => !s.contains 0#8) &&
  i.envp.all (fun s => !s.contains 0#8) &&
  !i.execfn.contains 0#8 &&
  (i.argv ++ i.envp).all (fun s => decide (s.length + 1 ≤ MAX_ARG_STRLEN)) &&
  decide (i.execfn.length < PATH_MAX) &&
  decide (argBytes i ≤ argLimit i.init.stackSize)

/-- Boolean mirror of `AuxvValid`. -/
def AuxvValid.check (a : AuxvConfig) : Bool :=
  (a.randomBytes.length == 16) &&
  (a.secure == 0#64) &&
  (a.uid == a.euid) &&
  (a.gid == a.egid) &&
  decide (a.extra.length ≤ 6) &&
  nodupCheck (a.extra.map Prod.fst) &&
  a.extra.all (fun e => !AuxvTag.fixedTags.contains e.1 && (e.1 != 0#64)) &&
  a.extra.all (fun e => e.1 != 33#64) &&
  (a.hwcap &&& 0x3#64 == 0x3#64) &&
  a.extra.all (fun e => (e.1 != 51#64) || decide (e.2.toNat ≤ 524288))

/-- Boolean mirror of `StackValid`. -/
def StackValid.check (init : ProcessInit) : Bool :=
  (init.stackTop.toNat % Obj.pageSize == 0) &&
  decide (init.stackTop.toNat ≤ TASK_SIZE) &&
  (init.stackSize % Obj.pageSize == 0) &&
  decide (init.stackSize ≤ init.stackTop.toNat) &&
  decide (STK_LIM ≤ init.stackSize) &&
  decide (init.stackSize ≤ STACK_SIZE_MAX) &&
  decide (STACK_BASE_MIN ≤ init.stackTop.toNat - init.stackSize)

/-- Kernel-reducible `Bool` mirror of `ProcessInit.Valid` (equivalence `ProcessInit.check_iff_valid`
    is proved in `ProofLib.Process`). -/
def ProcessInit.check (init : ProcessInit) : Bool :=
  AuxvValid.check init.auxv && StackValid.check init

/-- Boolean mirror of `SegValid`. -/
def SegValid.check (seg : String) : Bool :=
  (seg != "") && (seg != ".") && (seg != "..") &&
  seg.toList.all (fun c => (c != '/') && (c.toNat != 0) && decide (c.toNat < 256)) &&
  decide (seg.length ≤ NAME_MAX)

/-- Boolean mirror of `InputPathValid`. -/
def InputPathValid.check (p : String) : Bool :=
  !hasLeadingSlash p &&
  !(splitSlash p).isEmpty &&
  (splitSlash p).all SegValid.check

/-- Boolean mirror of `FsValid`. -/
def FsValid.check (i : ProcessInputs) : Bool :=
  i.dirs.all InputPathValid.check &&
  i.files.all (fun f => InputPathValid.check f.1) &&
  nodupCheck (i.files.map (fun f => normalizePath f.1)) &&
  i.files.all (fun f => decide (f.2.length ≤ MAX_LFS_FILESIZE)) &&
  i.files.all (fun f => i.dirs.all (fun d => !(normalizePath f.1).isPrefixOf (normalizePath d))) &&
  i.files.all (fun f => i.files.all (fun g =>
    !(normalizePath f.1).isPrefixOf (normalizePath g.1) || (normalizePath f.1 == normalizePath g.1)))

/-- Kernel-reducible `Bool` mirror of `ProcessInputs.Valid` (equivalence `ProcessInputs.check_iff_valid`
    is proved in `ProofLib.Process`). -/
def ProcessInputs.check (i : ProcessInputs) : Bool :=
  ArgsValid.check i && i.init.check && FsValid.check i

instance (seg : String) : Decidable (SegValid seg) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance (p : String) : Decidable (InputPathValid p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (i : ProcessInputs) : Decidable (ArgsValid i) :=
  match (inferInstance :
      Decidable (i.argv ≠ [] ∧
        ((∀ s ∈ i.argv, 0#8 ∉ s) ∧ (∀ s ∈ i.envp, 0#8 ∉ s) ∧ 0#8 ∉ i.execfn) ∧
        (∀ s ∈ i.argv ++ i.envp, s.length + 1 ≤ MAX_ARG_STRLEN) ∧
        i.execfn.length < PATH_MAX ∧
        argBytes i ≤ argLimit i.init.stackSize)) with
  | isTrue ⟨h1, h2, h3, h4, h5⟩ => isTrue ⟨h1, h2, h3, h4, h5⟩
  | isFalse hnot => isFalse fun h => hnot ⟨h.1, h.2, h.3, h.4, h.5⟩

instance (a : AuxvConfig) : Decidable (AuxvValid a) :=
  match (inferInstance :
      Decidable (a.randomBytes.length = 16 ∧
        a.secure = 0#64 ∧
        (a.uid = a.euid ∧ a.gid = a.egid) ∧
        a.extra.length ≤ 6 ∧
        ((a.extra.map Prod.fst).Pairwise (· ≠ ·) ∧
          ∀ e ∈ a.extra, e.1 ∉ AuxvTag.fixedTags ∧ e.1 ≠ 0#64) ∧
        (∀ e ∈ a.extra, e.1 ≠ 33#64) ∧
        a.hwcap &&& 0x3#64 = 0x3#64 ∧
        (∀ e ∈ a.extra, e.1 = 51#64 → e.2.toNat ≤ 524288))) with
  | isTrue ⟨h1, h2, h3, h4, h5, h33, h6, h7⟩ => isTrue ⟨h1, h2, h3, h4, h5, h33, h6, h7⟩
  | isFalse hnot => isFalse fun h => hnot ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩

instance (init : ProcessInit) : Decidable (StackValid init) :=
  match (inferInstance :
      Decidable ((init.stackTop.toNat % Obj.pageSize = 0 ∧ init.stackTop.toNat ≤ TASK_SIZE) ∧
        (init.stackSize % Obj.pageSize = 0 ∧ init.stackSize ≤ init.stackTop.toNat) ∧
        STK_LIM ≤ init.stackSize ∧
        init.stackSize ≤ STACK_SIZE_MAX ∧
        STACK_BASE_MIN ≤ init.stackTop.toNat - init.stackSize)) with
  | isTrue ⟨h1, h2, h3, h4, h5⟩ => isTrue ⟨h1, h2, h3, h4, h5⟩
  | isFalse hnot => isFalse fun h => hnot ⟨h.1, h.2, h.3, h.4, h.5⟩

instance (init : ProcessInit) : Decidable init.Valid :=
  inferInstanceAs (Decidable (AuxvValid init.auxv ∧ StackValid init))

instance : DecidablePred ProcessInit.Valid :=
  fun init => inferInstanceAs (Decidable init.Valid)

instance (i : ProcessInputs) : Decidable (FsValid i) :=
  match (inferInstance :
      Decidable (((∀ d ∈ i.dirs, InputPathValid d) ∧ (∀ f ∈ i.files, InputPathValid f.1)) ∧
        (i.files.map (fun f => normalizePath f.1)).Pairwise (· ≠ ·) ∧
        (∀ f ∈ i.files, f.2.length ≤ MAX_LFS_FILESIZE) ∧
        (∀ f ∈ i.files, ∀ d ∈ i.dirs, ¬ (normalizePath f.1 <+: normalizePath d)) ∧
        (∀ f ∈ i.files, ∀ g ∈ i.files,
          normalizePath f.1 <+: normalizePath g.1 → normalizePath f.1 = normalizePath g.1))) with
  | isTrue ⟨h1, h2, h3, h4, h5⟩ => isTrue ⟨h1, h2, h3, h4, h5⟩
  | isFalse hnot => isFalse fun h => hnot ⟨h.1, h.2, h.3, h.4, h.5⟩

instance (i : ProcessInputs) : Decidable i.Valid :=
  inferInstanceAs (Decidable (ArgsValid i ∧ i.init.Valid ∧ FsValid i))

instance : DecidablePred ProcessInputs.Valid :=
  fun i => inferInstanceAs (Decidable i.Valid)

end Arm64.Process


