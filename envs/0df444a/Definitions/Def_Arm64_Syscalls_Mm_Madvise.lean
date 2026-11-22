-- Prove2me | Definitions.Def_Arm64_Syscalls_Mm_Madvise
-- name    : Arm64_Syscalls_Mm_Madvise
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:09:12.344804+00:00
-- url     : https://prove2.me/theorems/ec7565f3-23c8-47d9-a351-dba49a6fac1a
-- title:
--   Arm64.Trusted.Syscalls.Mm.Madvise — Linux Virtual Memory madvise Syscall
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Mm/Madvise.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Mm/Madvise.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Mm/Madvise.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Mm/Madvise.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Mm/Madvise.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common
public import Definitions.Def_Arm64_Syscalls_Mm_Mmap

/-!
# Linux Virtual Memory `madvise` Syscall

Models the Linux `7.3` `madvise` (`__NR_madvise = 233`) syscall (`mm/madvise.c:2003` `do_madvise`),
including synchronous `MADV_DONTNEED` zero-fill (`Memory.zeroNonFrozen`), asynchronous `MADV_FREE`
lazy-reclaim marking (`Memory.madvFreeNonFrozen`, `mm/madvise.c:808` and `mm/rmap.c:2078`), and
no-op behavioral, transparent-hugepage, and coredump advice constants (`mm/madvise.c:1425`,
`include/uapi/asm-generic/mman-common.h:42`).
-/

@[expose] public section

namespace Arm64

namespace Memory

/-- Zero-fill all non-frozen mapped bytes in `[base, base + len)`, clearing `lazyFree := false` and
    preserving their protection bits (`m.perm`) and `anon` state; frozen and unmapped bytes (and
    bytes outside the range) are unchanged. Used for `madvise(..., MADV_DONTNEED)` on private
    anonymous memory (`mm/madvise.c:936` `madvise_dontneed_free`, which synchronously zaps PTEs so
    subsequent faults allocate fresh zero pages). Never touches frozen bytes. -/
def zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) : Memory :=
  ⟨fun a =>
    if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then
      some ((m.perm a).map (fun p => { p with anon := m.isAnon a }), 0#8)
    else
      m.cells a⟩

/-- Mark all non-frozen mapped bytes in `[base, base + len)` with `lazyFree := true`, preserving
    their protection bits (`m.perm`), `anon` state, and byte values; frozen and unmapped bytes (and
    bytes outside the range) are unchanged. Used for `madvise(..., MADV_FREE)` on private anonymous
    memory (`mm/madvise.c:808` `madvise_free_single_vma`, where Linux `7.3` marks folios `lazyfree`
    so `ttu_anon_lazyfree_folio` may asynchronously reclaim unwritten pages to zero at any later
    point until dirtied by a store). Never touches frozen bytes. -/
def madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) : Memory :=
  ⟨fun a =>
    if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then
      some ((m.perm a).map (fun p => { p with lazyFree := true, anon := m.isAnon a }), m.read8 a)
    else
      m.cells a⟩

end Memory

/-- Linux `madvise` `advice` constants (`include/uapi/asm-generic/mman-common.h:42-70`). -/
def MADV_NORMAL     : BitVec 64 := 0#64
def MADV_RANDOM     : BitVec 64 := 1#64
def MADV_SEQUENTIAL : BitVec 64 := 2#64
def MADV_WILLNEED   : BitVec 64 := 3#64
def MADV_DONTNEED   : BitVec 64 := 4#64
def MADV_FREE       : BitVec 64 := 8#64
def MADV_HUGEPAGE   : BitVec 64 := 14#64
def MADV_NOHUGEPAGE : BitVec 64 := 15#64
def MADV_DONTDUMP   : BitVec 64 := 16#64
def MADV_DODUMP     : BitVec 64 := 17#64

/-- Linux AArch64 `madvise` syscall number (`__NR_madvise = 233`, `include/uapi/asm-generic/unistd.h:642`, `mm/madvise.c:2003`). -/
def SYS_MADVISE : BitVec 64 := 233#64

/-- `madvise(addr, len, advice)` (`__NR_madvise = 233`, `mm/madvise.c:2003` `do_madvise`) on
    non-frozen mapped memory.
    Models:
    - `MADV_DONTNEED` (`4`): synchronously zero-fills private anonymous memory and clears `lazyFree`;
    - `MADV_FREE` (`8`): marks private anonymous memory `lazyFree := true` so reading before an
      intervening store fails closed (`.Exception`, preventing proofs from assuming `load1 == load2`
      across asynchronous `ttu_anon_lazyfree_folio` reclaim on Linux `7.3`);
    - pure behavioral, transparent-hugepage (`VM_HUGEPAGE` / `VM_NOHUGEPAGE`), and coredump hints
      (`MADV_NORMAL = 0`, `MADV_RANDOM = 1`, `MADV_SEQUENTIAL = 2`, `MADV_WILLNEED = 3`,
      `MADV_HUGEPAGE = 14`, `MADV_NOHUGEPAGE = 15`, `MADV_DONTDUMP = 16`, `MADV_DODUMP = 17`);
    - `[INTENTIONAL_SCOPE]`: `MADV_HUGEPAGE = 14` and `MADV_NOHUGEPAGE = 15` (`mm/huge_memory.c` /
      `mm/khugepaged.c` `hugepage_madvise`) assume a `CONFIG_TRANSPARENT_HUGEPAGE=y` Linux `7.3`
      kernel profile on normal user memory (`!VM_IO && !VM_PFNMAP && !VM_DAX`), where setting or
      clearing `VM_HUGEPAGE` / `VM_NOHUGEPAGE` always succeeds with `0` (whereas a kernel built with
      `CONFIG_TRANSPARENT_HUGEPAGE=n` or special device VMAs would return `-EINVAL`);
    - `[INTENTIONAL_SCOPE]`: `MADV_DONTNEED` and `MADV_FREE` on non-anonymous (`!isAnon`, e.g.
      file-backed ELF `.data`) memory fail closed with `.Exception "madvise on non-anonymous memory"`
      (on Linux `7.3`, `MADV_FREE` returns `-EINVAL` when `!vma_is_anonymous` in `mm/madvise.c:821`,
      and `MADV_DONTNEED` re-faults underlying file bytes instead of zeroing); all other `advice`
      values fail closed with `.Exception "unmodeled madvise advice"`. -/
def execMadvise (s : State) : State :=
  let rawStart := s.readReg64 Reg.x0
  let addr := untaggedAddr rawStart
  let len := (s.readReg64 Reg.x1).toNat
  let advice := (s.readReg32 Reg.x2).signExtend 64
  let size := pageAlignUp len
  let isNoopHint :=
    advice == MADV_NORMAL || advice == MADV_RANDOM || advice == MADV_SEQUENTIAL ||
    advice == MADV_WILLNEED || advice == MADV_HUGEPAGE || advice == MADV_NOHUGEPAGE ||
    advice == MADV_DONTDUMP || advice == MADV_DODUMP
  if advice != MADV_DONTNEED && advice != MADV_FREE && !isNoopHint then
    s.setStatus (.Exception "unmodeled madvise advice")
  else if rawStart.toNat % PAGE_SIZE != 0 || !decide (len ≤ 2 ^ 64 - PAGE_SIZE) ||
      !decide (rawStart.toNat + size < 2 ^ 64) then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if len == 0 then
    (s.writeReg64 Reg.x0 0#64).advancePC
  else if !decide (addr.toNat + size ≤ 2 ^ 48) then
    s.setStatus (.Exception "madvise range exceeds user VA space")
  else if !s.mem.allPerm (fun p => !p.frozen) addr size then
    s.setStatus (.Exception "madvise on frozen memory")
  else if !s.mem.allPerm (·.mapped) addr size then
    if s.mem.canMap addr size then
      (s.writeReg64 Reg.x0 (-ENOMEM)).advancePC
    else
      s.setStatus (.Exception "madvise on partially mapped range")
  else if (advice == MADV_DONTNEED || advice == MADV_FREE) && !s.mem.allAnon addr size then
    s.setStatus (.Exception "madvise on non-anonymous memory")
  else if advice == MADV_DONTNEED then
    ((s.setMem (s.mem.zeroNonFrozen addr size)).writeReg64 Reg.x0 0#64).advancePC
  else if advice == MADV_FREE then
    ((s.setMem (s.mem.madvFreeNonFrozen addr size)).writeReg64 Reg.x0 0#64).advancePC
  else
    (s.writeReg64 Reg.x0 0#64).advancePC

end Arm64


