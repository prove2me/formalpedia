-- Prove2me | Definitions.Def_Arm64_Syscalls_Mm_Mremap
-- name    : Arm64_Syscalls_Mm_Mremap
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:08:57.918043+00:00
-- url     : https://prove2.me/theorems/d313ddf4-d463-4e23-ba0c-205bfd590041
-- title:
--   Arm64.Trusted.Syscalls.Mm.Mremap — Linux Virtual Memory mremap Syscall
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Mm/Mremap.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Mm/Mremap.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Mm/Mremap.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Mm/Mremap.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Mm/Mremap.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common
public import Definitions.Def_Arm64_Syscalls_Mm_Mmap

/-!
# Linux Virtual Memory `mremap` Syscall

Trusted model of the Linux AArch64 `mremap` syscall (`mm/mremap.c`,
`include/uapi/linux/mman.h`), defining `Memory.remapRw`, `SYS_MREMAP`, `MREMAP_MAYMOVE`,
and `execMremap`.
-/

@[expose] public section

namespace Arm64

namespace Memory

/-- Move or resize a non-frozen `Perm.rw` range `[oldBase, oldBase + oldSize)` onto
    `[newBase, newBase + newSize)`:
    - frozen bytes (`(m.perm a).frozen`) are unconditionally preserved;
    - for any non-frozen byte `a` in `[newBase, newBase + newSize)` at offset
      `off := (a - newBase).toNat`, maps `some (some p, b)` where for `off < oldSize` (`src :=
      oldBase + off`) `b = m.read8 src` and `p = { Perm.rw with lazyFree := m.isLazyFree src,
      anon := m.isAnon src }`, and for `off ≥ oldSize` `b = 0#8` and `p = Perm.rw`;
    - for any remaining non-frozen byte `a` in `[oldBase, oldBase + oldSize)`, unmaps (`none`);
    - all other bytes keep `m.cells a`. -/
def remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) : Memory :=
  ⟨fun a =>
    if (m.perm a).frozen then
      m.cells a
    else if (a - newBase).toNat < newSize then
      let off := (a - newBase).toNat
      let src := oldBase + BitVec.ofNat 64 off
      let b := if off < oldSize then m.read8 src else 0#8
      let p := if off < oldSize then
        { Perm.rw with lazyFree := m.isLazyFree src, anon := m.isAnon src }
      else Perm.rw
      some (some p, b)
    else if (a - oldBase).toNat < oldSize then
      none
    else
      m.cells a⟩

end Memory

/-- Linux AArch64 `mremap` syscall number (`__NR_mremap = 216`,
    `include/uapi/asm-generic/unistd.h:597`, `mm/mremap.c:1964`). -/
def SYS_MREMAP : BitVec 64 := 216#64

/-- `mremap` `flags` bit `MREMAP_MAYMOVE` (`1`, `include/uapi/linux/mman.h:8`). -/
def MREMAP_MAYMOVE : BitVec 64 := 1#64

/-- `mremap(old_address, old_size, new_size, flags)` (`__NR_mremap = 216`,
    `SYSCALL_DEFINE5(mremap)`, `do_mremap`, and `mremap_at` in `mm/mremap.c:1559,1641,1679,2022`),
    modeled for `flags == 0` (in-place resize) and `flags == MREMAP_MAYMOVE` (`1`) on a single
    mapped `Perm.rw` anonymous range:
    - `[INTENTIONAL_SCOPE]`: any `flags ≠ 0` and `flags ≠ MREMAP_MAYMOVE` fails closed with
      `.Exception "unmodeled mremap flags"`;
    - with `oldAddr := untaggedAddr X0`, `oldAligned := pageAlignUp oldLen`, and
      `newAligned := pageAlignUp newLen`:
      - strips any AArch64 user TBI tag from `oldAddr := untaggedAddr X0` (`mm/mremap.c:2096`);
      - rejects unaligned `oldAddr`, `newLen == 0`, or `newLen > USER_VA_LIMIT` (`PAGE_ALIGN(new_len)
        == 0 || PAGE_ALIGN(new_len) > TASK_SIZE` in `check_mremap_params`, `mm/mremap.c:2028-2045`)
        with `-EINVAL`;
      - fails closed with `.Exception "unmodeled mremap (old_size == 0)"` when `oldLen == 0` or
        `oldLen > 2 ^ 64 - PAGE_SIZE` (where C `PAGE_ALIGN(old_len)` wraps to `0`);
      - `[INTENTIONAL_OVERAPPROX]`: queries `s.oracle.mremapRefusal s.oracleIdx == some .enomem`
        immediately after `check_mremap_params`, consuming `s.nextOracle` and returning `-ENOMEM`
        (`check_map_count_against_split_early` before `vma_lookup`, `mm/mremap.c:2039-2042`, plus
        later `may_expand_vm` refusals at `mm/mremap.c:1870`);
      - when `oldAddr.toNat + oldAligned > USER_VA_LIMIT`: returns `-EFAULT` if the starting page
        at `oldAddr` is above `USER_VA_LIMIT` or unmapped (`vma_lookup` miss), returns `oldAddr` on
        `newAligned == oldAligned` (`MREMAP_NO_RESIZE`, `mm/mremap.c:1688`), returns `-EINVAL` on
        `newAligned < oldAligned` (`MREMAP_SHRINK` -> `shrink_vma` -> `do_vmi_munmap`,
        `mm/mremap.c:897-906,1805`, `mm/vma.c:1717`, regardless of `MREMAP_MAYMOVE`), and returns
        `-EFAULT` on `newAligned > oldAligned` (`old_len > vma->vm_end - addr`, `mm/mremap.c:1849`);
      - if `[oldAddr, oldAddr + oldAligned)` intersects any frozen byte, fails closed with
        `.Exception "mremap on frozen memory"`;
      - if `[oldAddr, oldAddr + oldAligned)` is completely unmapped (`s.mem.canMap oldAddr oldAligned`),
        returns `-EFAULT` (`vma_lookup` miss in `check_prep_vma`, `mm/mremap.c:1787,2047`);
      - if `[oldAddr, oldAddr + oldAligned)` is not uniformly `some Perm.rw` or not anonymous,
        fails closed with `.Exception`;
      - `[INTENTIONAL_OVERAPPROX]`: if `s.oracle.mremapRefusal s.oracleIdx == some .efault`,
        consumes `s.nextOracle`, leaves `s.mem` unchanged, and returns `-EFAULT`
        (`old_len > vma->vm_end - addr` in `check_prep_vma`, `mm/mremap.c:1849`, over-approximating
        adjacent anonymous mappings that remain unmerged `vm_area_struct`s in the kernel maple tree);
      - otherwise (`mremapRefusal == none`): proceeds with in-place resize (`flags == 0`) or
        `MREMAP_MAYMOVE` relocation via `sanitizeMmapAddr mUnmapped cand newAligned`. -/
def execMremap (s : State) : State :=
  let oldAddr := untaggedAddr (s.readReg64 Reg.x0)
  let oldLen  := (s.readReg64 Reg.x1).toNat
  let newLen  := (s.readReg64 Reg.x2).toNat
  let flags   := s.readReg64 Reg.x3
  if flags != 0#64 && flags != MREMAP_MAYMOVE then
    s.setStatus (.Exception "unmodeled mremap flags")
  else if oldAddr.toNat % PAGE_SIZE != 0 || newLen == 0 || !decide (newLen ≤ USER_VA_LIMIT) then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if oldLen == 0 || !decide (oldLen ≤ 2 ^ 64 - PAGE_SIZE) then
    s.setStatus (.Exception "unmodeled mremap (old_size == 0)")
  else if s.oracle.mremapRefusal s.oracleIdx == some .enomem then
    ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC
  else
    let oldAligned := pageAlignUp oldLen
    let newAligned := pageAlignUp newLen
    if !decide (oldAddr.toNat + oldAligned ≤ USER_VA_LIMIT) then
      if !decide (oldAddr.toNat < USER_VA_LIMIT) || s.mem.canMap oldAddr PAGE_SIZE then
        ((s.nextOracle).writeReg64 Reg.x0 EFAULT_RET).advancePC
      else if newAligned == oldAligned then
        ((s.nextOracle).writeReg64 Reg.x0 oldAddr).advancePC
      else if decide (newAligned < oldAligned) then
        ((s.nextOracle).writeReg64 Reg.x0 (-EINVAL)).advancePC
      else
        ((s.nextOracle).writeReg64 Reg.x0 EFAULT_RET).advancePC
    else if !s.mem.allPerm (fun p => !p.frozen) oldAddr oldAligned then
      s.setStatus (.Exception "mremap on frozen memory")
    else if s.mem.canMap oldAddr oldAligned then
      ((s.nextOracle).writeReg64 Reg.x0 EFAULT_RET).advancePC
    else if !s.mem.allPerm (· == some Perm.rw) oldAddr oldAligned then
      s.setStatus (.Exception "unmodeled mremap (range not uniformly PROT_READ|PROT_WRITE)")
    else if !s.mem.allAnon oldAddr oldAligned then
      s.setStatus (.Exception "unmodeled mremap on non-anonymous memory")
    else if s.oracle.mremapRefusal s.oracleIdx == some .efault then
      ((s.nextOracle).writeReg64 Reg.x0 EFAULT_RET).advancePC
    else if flags == 0#64 then
      if decide (newAligned ≤ oldAligned) then
        let mem' := s.mem.remapRw oldAddr oldAligned oldAddr newAligned
        ((((s.setMem mem').setPhysMemAvail
          (s.physMemAvail + oldAligned - newAligned)).nextOracle).writeReg64
          Reg.x0 oldAddr).advancePC
      else if !decide (oldAddr.toNat + newAligned ≤ USER_VA_LIMIT) ||
          !s.mem.canMap (oldAddr + BitVec.ofNat 64 oldAligned) (newAligned - oldAligned) then
        ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC
      else if !decide (newAligned ≤ s.physMemAvail + oldAligned) then
        s.setStatus .OutOfMemory
      else
        let mem' := s.mem.remapRw oldAddr oldAligned oldAddr newAligned
        ((((s.setMem mem').setPhysMemAvail
          (s.physMemAvail + oldAligned - newAligned)).nextOracle).writeReg64
          Reg.x0 oldAddr).advancePC
    else
      let mUnmapped := s.mem.unmapNonFrozen oldAddr oldAligned
      match sanitizeMmapAddr mUnmapped (s.oracle.mmap s.oracleIdx) newAligned with
      | none =>
        ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC
      | some newBase =>
        if !decide (newAligned ≤ s.physMemAvail + oldAligned) then
          s.setStatus .OutOfMemory
        else
          let mem' := s.mem.remapRw oldAddr oldAligned newBase newAligned
          ((((s.setMem mem').setPhysMemAvail
            (s.physMemAvail + oldAligned - newAligned)).nextOracle).writeReg64
            Reg.x0 newBase).advancePC

end Arm64


