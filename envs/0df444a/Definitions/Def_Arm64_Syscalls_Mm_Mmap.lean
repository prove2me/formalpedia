-- Prove2me | Definitions.Def_Arm64_Syscalls_Mm_Mmap
-- name    : Arm64_Syscalls_Mm_Mmap
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:08:25.8651+00:00
-- url     : https://prove2.me/theorems/682ff419-a3ec-4b93-891c-522bafef022a
-- title:
--   Arm64.Trusted.Syscalls.Mm.Mmap — Linux Virtual Memory brk, mmap, & munmap Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Mm/Mmap.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Mm/Mmap.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Mm/Mmap.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Mm/Mmap.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Mm/Mmap.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Linux Virtual Memory `brk`, `mmap`, & `munmap` Syscalls (`Arm64.Trusted.Syscalls.Mm.Mmap`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Linux `7.3` Upstream Sources**:
  - `mm/mmap.c:115` (`SYSCALL_DEFINE1(brk, unsigned long, brk)` -> `check_brk_limits` -> `do_brk_flags` / `do_brk_munmap`)
  - `mm/mmap.c:1661` (`SYSCALL_DEFINE6(mmap_pgoff)` / `ksys_mmap_pgoff` -> `vm_mmap_pgoff` -> `do_mmap`)
  - `mm/vma.c:1718` (`do_vmi_munmap` / `vm_munmap`, invoked from `mm/mmap.c` `SYSCALL_DEFINE2(munmap)`)
  - `include/uapi/asm-generic/mman-common.h:10` (`PROT_NONE = 0x0`, `PROT_READ | PROT_WRITE = 0x3`, `MAP_PRIVATE | MAP_ANONYMOUS = 0x22`, `MAP_STACK = 0x20000`, `MAP_FIXED = 0x10`)
  - `include/linux/mman.h:158` (`calc_vm_flag_bits`: `MAP_STACK` maps to advisory `VM_NOHUGEPAGE`)
- **Purpose & Key Exports**: `Memory.unmapNonFrozen`,
  `Memory.setPermNonFrozen`, `PAGE_SIZE`, `USER_VA_LIMIT`, `pageAlignUp`, `MMAP_PROT_NONE`,
  `MMAP_PROT_RW`, `MMAP_FLAGS_PRIVATE_ANON`, `MMAP_FLAGS_PRIVATE_ANON_STACK`, `MAP_FIXED`,
  `MMAP_FLAGS_PRIVATE_ANON_FIXED`,
  `MMAP_MIN_ADDR`, `SYS_BRK` (`214`), `SYS_MUNMAP` (`215`), `SYS_MMAP` (`222`), `findMappedByte`,
  `findUnmappedAreaLoop`, `findUnmappedArea`, `sanitizeMmapAddr`, `execMmap`, `execMunmap`,
  and `execBrk`.
-/

@[expose] public section

namespace Arm64

namespace Memory

/-- Unmap all non-frozen bytes of `[base, base + len)` (they lose their cell); frozen bytes
    (`some Perm.ro`, `some Perm.rx`) and bytes outside the range are unchanged. Used for `munmap`
    (`do_vmi_munmap` in `mm/vma.c:1718`), which unmaps both `Perm.rw` and `Perm.protNone` pages
    while leaving already-unmapped holes unmapped. Never touches frozen bytes. -/
def unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) : Memory :=
  ⟨fun a => if (a - base).toNat < len && !(m.perm a).frozen then none else m.cells a⟩

/-- Set the permission of all non-frozen mapped bytes in `[base, base + len)` to `p`'s protection
    bits, preserving their byte values, `lazyFree` state, and `anon` state; frozen and unmapped
    bytes (and bytes outside the range) are unchanged. Used for `mprotect` transitions between
    `Perm.rw` and `Perm.protNone` (`mm/mprotect.c` `change_protection`, which updates PTE protection
    bits without clearing `folio_test_lazyfree` or changing VMA `vm_ops`). Never touches frozen bytes. -/
def setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) : Memory :=
  ⟨fun a =>
    if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then
      some (some { p with lazyFree := m.isLazyFree a, anon := m.isAnon a }, m.read8 a)
    else
      m.cells a⟩

end Memory

/-- Linux page size on AArch64 (4 KiB granule, `arch/arm64/include/asm/page-def.h:16`). -/
def PAGE_SIZE : Nat := 4096

/-- Round `n` up to a multiple of `PAGE_SIZE`. -/
def pageAlignUp (n : Nat) : Nat := (n + (PAGE_SIZE - 1)) / PAGE_SIZE * PAGE_SIZE

/-- `mmap` / `mprotect` `prot` argument `PROT_NONE` (`0x0`, `include/uapi/asm-generic/mman-common.h:13`). -/
def MMAP_PROT_NONE : BitVec 64 := 0x0#64

/-- `mmap` / `mprotect` `prot` argument `PROT_READ | PROT_WRITE` (`0x3`, `include/uapi/asm-generic/mman-common.h:10-11`). -/
def MMAP_PROT_RW : BitVec 64 := 0x3#64

/-- `mmap` `flags` argument `MAP_PRIVATE | MAP_ANONYMOUS` (`0x22`, `include/uapi/asm-generic/mman-common.h:20-23`). -/
def MMAP_FLAGS_PRIVATE_ANON : BitVec 64 := 0x22#64

/-- `mmap` `flags` argument `MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK`
    (`0x20022`, `include/uapi/asm-generic/mman-common.h:20-28`; `MAP_STACK = 0x20000` maps only to
    advisory `VM_NOHUGEPAGE` in `include/linux/mman.h:158-159`). -/
def MMAP_FLAGS_PRIVATE_ANON_STACK : BitVec 64 := 0x20022#64

/-- `mmap` `flags` bit `MAP_FIXED` (`0x10`, `include/uapi/asm-generic/mman-common.h:22`). -/
def MAP_FIXED : BitVec 64 := 0x10#64

/-- `mmap` `flags` argument `MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED`
    (`0x32 = MMAP_FLAGS_PRIVATE_ANON ||| MAP_FIXED`). -/
def MMAP_FLAGS_PRIVATE_ANON_FIXED : BitVec 64 := 0x32#64

/-- Lowest address at which the model starts any `mmap` / `mremap` mapping (`65536`): the
    `MAP_FIXED` lower bound in `execMmap`, the floor of oracle candidates accepted by
    `sanitizeMmapAddr`, and the start of the `findUnmappedArea` gap search. Linux refuses lower
    addresses to processes without `CAP_SYS_RAWIO` (`cap_mmap_addr` in `security/commoncap.c`
    checks `dac_mmap_min_addr`, the `vm.mmap_min_addr` sysctl; `CONFIG_LSM_MMAP_MIN_ADDR` adds
    a second bound). `65536` is the value Debian, Ubuntu and Fedora set and the default
    `CONFIG_LSM_MMAP_MIN_ADDR`; the model assumes the effective bound is exactly this value
    (`MAP_FIXED` below it fails closed, and non-fixed placements never land below it). -/
def MMAP_MIN_ADDR : Nat := 65536

/-- Linux AArch64 `brk` syscall number (`__NR_brk = 214`, `include/uapi/asm-generic/unistd.h:593`, `mm/mmap.c:115`). -/
def SYS_BRK : BitVec 64 := 214#64

/-- Linux AArch64 `munmap` syscall number (`__NR_munmap = 215`, `include/uapi/asm-generic/unistd.h:595`, `mm/vma.c:1718`). -/
def SYS_MUNMAP : BitVec 64 := 215#64

/-- Linux AArch64 `mmap` syscall number (`__NR_mmap = 222`, `include/uapi/asm-generic/unistd.h:609`, `mm/mmap.c:1661`). -/
def SYS_MMAP : BitVec 64 := 222#64

/-- Smallest byte offset `curOff ≤ off < curOff + rem` such that
    `(m.perm (base + BitVec.ofNat 64 off)).mapped = true`, or `none` if
    `[base + curOff, base + curOff + rem)` is completely unmapped. Tail-recursive so large probes
    run in constant stack space. -/
def findMappedByte (m : Memory) (base : BitVec 64) (curOff : Nat) : Nat → Option Nat
  | 0 => none
  | rem + 1 =>
    if (m.perm (base + BitVec.ofNat 64 curOff)).mapped then some curOff
    else findMappedByte m base (curOff + 1) rem

/-- Low-to-high page-aligned gap search over `[addr, USER_VA_LIMIT)` (`vm_unmapped_area` in
    `mm/mmap.c`), advancing past the page containing any mapped byte on collision. -/
def findUnmappedAreaLoop (m : Memory) (size : Nat) : Nat → Nat → Option (BitVec 64)
  | 0, _ => none
  | fuel + 1, addr =>
    if !decide (addr + size ≤ USER_VA_LIMIT) then
      none
    else
      let base := BitVec.ofNat 64 addr
      match findMappedByte m base 0 size with
      | none => some base
      | some off =>
        let nextPage := ((addr + off) / PAGE_SIZE + 1) * PAGE_SIZE
        findUnmappedAreaLoop m size fuel nextPage

/-- Lowest page-aligned unmapped range `[base, base + size)` within `[MMAP_MIN_ADDR, USER_VA_LIMIT)`
    (`arch_get_unmapped_area` / `vm_unmapped_area` in `mm/mmap.c`), or `none` when `size = 0`,
    `size` is not page-aligned, or no free gap of `size` bytes exists. -/
def findUnmappedArea (m : Memory) (size : Nat) : Option (BitVec 64) :=
  if size == 0 || size % PAGE_SIZE != 0 then
    none
  else
    findUnmappedAreaLoop m size ((USER_VA_LIMIT - MMAP_MIN_ADDR) / PAGE_SIZE + 1) MMAP_MIN_ADDR

/-- Sanitize an oracle `mmap` / `mremap` placement candidate `cand` for a page-aligned request of
    `size` bytes (`size > 0`, `size % PAGE_SIZE = 0`, `mm/mmap.c` `get_unmapped_area` ->
    `security_mmap_addr`):
    - if `MMAP_MIN_ADDR ≤ cand.toNat`, `cand` is `PAGE_SIZE`-aligned, `cand.toNat + size ≤ USER_VA_LIMIT`,
      and `m.canMap cand size = true`, accepts `cand` directly;
    - otherwise substitutes `findUnmappedArea m size`, returning `none` only when no unmapped
      page-aligned range of `size` bytes fits in `[MMAP_MIN_ADDR, USER_VA_LIMIT)`. -/
def sanitizeMmapAddr (m : Memory) (cand : BitVec 64) (size : Nat) : Option (BitVec 64) :=
  if size == 0 || size % PAGE_SIZE != 0 then
    none
  else if decide (MMAP_MIN_ADDR ≤ cand.toNat) && cand.toNat % PAGE_SIZE == 0 &&
      decide (cand.toNat + size ≤ USER_VA_LIMIT) && m.canMap cand size then
    some cand
  else
    findUnmappedArea m size

/-- Anonymous private `mmap(addr, len, prot, flags, fd, 0)` (`__NR_mmap = 222`, `mm/mmap.c:1661`
    `ksys_mmap_pgoff` -> `do_mmap`) with `prot ∈ {PROT_NONE (0), PROT_READ | PROT_WRITE (3)}` and
    `flags ∈ {MAP_PRIVATE | MAP_ANONYMOUS (0x22), MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK (0x20022),
    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED (0x32)}` (`MAP_STACK` is an advisory `VM_NOHUGEPAGE`
    no-op on Linux AArch64; `MAP_FIXED | MAP_STACK = 0x20032` remains fail-closed).
    Linux ignores `fd` for anonymous mappings, and so does the model. With `size := pageAlignUp len`
    and `newPerm := Perm.protNone` when `prot = 0`, `Perm.rw` when `prot = 3`:
    - `[INTENTIONAL_SCOPE]`: other `prot`/`flags`/offset combinations (file mappings, `MAP_SHARED`,
      `PROT_READ` alone, `PROT_EXEC`, a non-zero offset, ...) are unmodeled and raise `.Exception`
      rather than being silently approximated;
    - `len = 0` returns `-EINVAL` without consulting the oracle;
    - **without `MAP_FIXED`**, Linux treats `addr` as a hint only; the model ignores it and sanitizes
      `cand := s.oracle.mmap s.oracleIdx` (`[INTENTIONAL_OVERAPPROX]`) via `sanitizeMmapAddr s.mem cand size`
      (`mm/mmap.c` `get_unmapped_area`); when no free gap of `size` bytes exists (`none`), it
      transitions to the terminal `ExecStatus.OutOfMemory` outcome (`s.setStatus .OutOfMemory`);
    - **with `MAP_FIXED`** (used for `PROT_NONE` guard pages and `PROT_READ | PROT_WRITE`
      demand-zero page overlays), `addr` must be page-aligned within `[MMAP_MIN_ADDR, 2 ^ 48 - size]`
      (`mm/mmap.c` `get_unmapped_area` -> `security_mmap_addr`) and touch no frozen bytes. With
      `reclaimed := s.mem.countRw addr size`, `prot = PROT_NONE` replaces `[addr, addr + size)`
      with zero-filled `Perm.protNone` pages and refunds `reclaimed` to `s.physMemAvail`;
      `prot = PROT_READ | PROT_WRITE` transitions to `ExecStatus.OutOfMemory` when
      `size > s.physMemAvail + reclaimed`, and otherwise replaces `[addr, addr + size)` with
      zero-filled `Perm.rw` pages and sets `s.physMemAvail := s.physMemAvail + reclaimed - size`.
    - **Physical memory accounting (`s.physMemAvail`)**: `PROT_NONE` mappings consume `0` physical
      bytes (`accountable_mapping` in `mm/mmap.c`); `PROT_READ | PROT_WRITE` mappings deduct the net
      newly committed writable bytes (`size` for non-fixed mappings, `size - reclaimed` net for
      `MAP_FIXED`) from `s.physMemAvail`, transitioning to `ExecStatus.OutOfMemory` if insufficient. -/
def execMmap (s : State) : State :=
  let len := (s.readReg64 Reg.x1).toNat
  let prot := s.readReg64 Reg.x2
  let flags := s.readReg64 Reg.x3
  if (prot != MMAP_PROT_RW && prot != MMAP_PROT_NONE) ||
      (flags != MMAP_FLAGS_PRIVATE_ANON && flags != MMAP_FLAGS_PRIVATE_ANON_STACK &&
        flags != MMAP_FLAGS_PRIVATE_ANON_FIXED) ||
      s.readReg64 Reg.x5 != 0#64 then
    s.setStatus (.Exception "unmodeled mmap (only anonymous private mappings, PROT_NONE or PROT_READ|PROT_WRITE)")
  else if len == 0 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if flags == MMAP_FLAGS_PRIVATE_ANON_FIXED then
    let addr := s.readReg64 Reg.x0
    let size := pageAlignUp len
    if addr.toNat % PAGE_SIZE != 0 || addr.toNat < MMAP_MIN_ADDR ||
        !decide (addr.toNat + size ≤ 2 ^ 48) then
      s.setStatus (.Exception "unmodeled MAP_FIXED address")
    else if !s.mem.allPerm (fun p => !p.frozen) addr size then
      s.setStatus (.Exception "MAP_FIXED on frozen memory")
    else
      let reclaimed := s.mem.countRw addr size
      if prot == MMAP_PROT_NONE then
        (((s.setMem (((s.mem.unmapNonFrozen addr size).mapZero addr size).setPermNonFrozen addr size
          Perm.protNone)).setPhysMemAvail (s.physMemAvail + reclaimed)).writeReg64 Reg.x0 addr).advancePC
      else if !decide (size ≤ s.physMemAvail + reclaimed) then
        s.setStatus .OutOfMemory
      else
        (((s.setMem ((s.mem.unmapNonFrozen addr size).mapZero addr size)).setPhysMemAvail
          (s.physMemAvail + reclaimed - size)).writeReg64 Reg.x0 addr).advancePC
  else
    let size := pageAlignUp len
    match sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) size with
    | some base =>
      if prot == MMAP_PROT_NONE then
        (((s.setMem ((s.mem.mapZero base size).setPermNonFrozen base size Perm.protNone)).nextOracle).writeReg64
          Reg.x0 base).advancePC
      else if !decide (size ≤ s.physMemAvail) then
        s.setStatus .OutOfMemory
      else
        ((((s.setMem (s.mem.mapZero base size)).setPhysMemAvail
          (s.physMemAvail - size)).nextOracle).writeReg64 Reg.x0 base).advancePC
    | none =>
      s.setStatus .OutOfMemory

/-- `munmap(addr, len)` (`__NR_munmap = 215`, `mm/mmap.c:1093` `vm_munmap` -> `mm/vma.c:1718`
    `do_vmi_munmap`).
    Strips any AArch64 user TBI tag via `addr := untaggedAddr X0` (`mm/mmap.c:1093`), and with
    `size := pageAlignUp len`:
    - if `addr` is not page-aligned (`addr.toNat % PAGE_SIZE != 0`), `len == 0`, or
      `[addr, addr + size)` exceeds the 48-bit user virtual address space
      (`addr.toNat + size > 2 ^ 48`), returns `-EINVAL`;
    - `[INTENTIONAL_SCOPE]`: if `[addr, addr + size)` intersects any frozen byte (`some Perm.ro` or
      `some Perm.rx`), fails closed with `.Exception "munmap on frozen memory"`;
    - otherwise unmaps all non-frozen bytes in `[addr, addr + size)` (`s.mem.unmapNonFrozen addr size`,
      allowing already-unmapped holes in the range per POSIX/Linux), refunds
      `s.mem.countRw addr size` to `s.physMemAvail`, and returns `0`. -/
def execMunmap (s : State) : State :=
  let addr := untaggedAddr (s.readReg64 Reg.x0)
  let len := (s.readReg64 Reg.x1).toNat
  let size := pageAlignUp len
  if addr.toNat % PAGE_SIZE != 0 || len == 0 || !decide (addr.toNat + size ≤ 2 ^ 48) then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if !s.mem.allPerm (fun p => !p.frozen) addr size then
    s.setStatus (.Exception "munmap on frozen memory")
  else
    let reclaimed := s.mem.countRw addr size
    (((s.setMem (s.mem.unmapNonFrozen addr size)).setPhysMemAvail
      (s.physMemAvail + reclaimed)).writeReg64 Reg.x0 0#64).advancePC

/-- `256`-page (`1 MiB = 1,048,576` B) virtual-address guard gap above `newPage` enforced by
    `execBrk` (`stack_guard_gap = 256UL << PAGE_SHIFT` in `mm/mmap.c:186` `vm_start_gap(next)`),
    subsuming both the 1-page `find_vma_intersection(mm, oldbrk, newbrk + PAGE_SIZE)` guard against
    ordinary VMAs and the 256-page `VM_GROWSDOWN` guard below the stack VMA. -/
def BRK_GUARD_GAP : Nat := 256 * PAGE_SIZE

/-- `brk(addr)` (`__NR_brk = 214`, `mm/mmap.c:115` `SYSCALL_DEFINE1(brk)` -> `do_brk_flags` /
    `do_brk_munmap`): query or adjust the program break without consulting `Oracle`.
    - `[INTENTIONAL_SCOPE]`: models single-threaded user-space execution under
      `RLIMIT_DATA = RLIM_INFINITY` and `RLIMIT_AS = RLIM_INFINITY` (`check_data_rlimit` in
      `mm/mmap.c:134`, `may_expand_vm` in `mm/vma.c:3028`), `mm->map_count ≤ sysctl_max_map_count`
      (`mm/vma.c:3031`), and no active `MCL_FUTURE` (`mlock_future_ok` in `mm/vma.c:3034`).
    - Query or below-base (`addr = 0` or `addr < s.brkStart`): returns the current break `s.brk`
      with memory and `s.brk` unchanged.
    - Shrink or same-page (`newPage ≤ oldPage`, where `oldPage := pageAlignUp s.brk.toNat` and
      `newPage := pageAlignUp addr.toNat`, `shrinkBytes := oldPage - newPage`):
      - if `newPage == oldPage` (`mm/mmap.c:145`), updates `s.brk := addr` and returns `addr`;
      - if `newPage < oldPage` and `[newPage, oldPage)` contains no mapped byte
        (`s.mem.canMap (BitVec.ofNat 64 newPage) shrinkBytes`, e.g. after `munmap` of the entire
        heap tail, matching `!brkvma || brkvma->vm_start >= oldbrk` in `mm/mmap.c:167`),
        returns the unchanged `s.brk` (`origbrk`) with memory and `physMemAvail` unchanged;
      - if `newPage < oldPage` and `[newPage, oldPage)` intersects any frozen byte, fails closed
        with `.Exception "brk shrink on frozen memory"`;
      - otherwise unmaps all non-frozen pages `[newPage, oldPage)` (`s.mem.unmapNonFrozen`,
        `do_brk_munmap` in `mm/mmap.c:155`), refunds `s.mem.countRw newPage shrinkBytes` to
        `s.physMemAvail`, sets `s.brk := addr`, and returns `addr`.
    - Grow (`oldPage < newPage`, `growBytes := newPage - oldPage`):
      1. **VMA collision + `BRK_GUARD_GAP` (`256 * PAGE_SIZE = 1 MiB`) guard gap**
         (`newbrk + PAGE_SIZE > vm_start_gap(next)` in `mm/mmap.c:186`): if
         `newPage + BRK_GUARD_GAP > USER_VA_LIMIT` or
         `!s.mem.canMap (BitVec.ofNat 64 oldPage) (growBytes + BRK_GUARD_GAP)`, returns the
         unchanged `s.brk` in `X0` with `status = .Running` so allocators
         deterministically fall back to `SYS_mmap`.
      2. **Physical memory budget**: if `s.physMemAvail < growBytes`, transitions to
         `ExecStatus.OutOfMemory`.
      3. Otherwise maps `[oldPage, newPage)` read-write and zero-filled (`s.mem.mapZero`), deducts
         `growBytes` from `s.physMemAvail`, sets `s.brk := addr`, and returns `addr`. -/
def execBrk (s : State) : State :=
  let addr := s.readReg64 Reg.x0
  if addr == 0#64 || addr.ult s.brkStart then
    (s.writeReg64 Reg.x0 s.brk).advancePC
  else
    let oldPage := pageAlignUp s.brk.toNat
    let newPage := pageAlignUp addr.toNat
    if newPage == oldPage then
      ((s.setBrk addr).writeReg64 Reg.x0 addr).advancePC
    else if newPage < oldPage then
      let shrinkBase := BitVec.ofNat 64 newPage
      let shrinkBytes := oldPage - newPage
      if s.mem.canMap shrinkBase shrinkBytes then
        (s.writeReg64 Reg.x0 s.brk).advancePC
      else if !s.mem.allPerm (fun p => !p.frozen) shrinkBase shrinkBytes then
        s.setStatus (.Exception "brk shrink on frozen memory")
      else
        let reclaimed := s.mem.countRw shrinkBase shrinkBytes
        let mem := s.mem.unmapNonFrozen shrinkBase shrinkBytes
        ((((s.setBrk addr).setMem mem).setPhysMemAvail (s.physMemAvail + reclaimed)).writeReg64
          Reg.x0 addr).advancePC
    else
      let growBytes := newPage - oldPage
      if !decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT) ||
          !s.mem.canMap (BitVec.ofNat 64 oldPage) (growBytes + BRK_GUARD_GAP) then
        (s.writeReg64 Reg.x0 s.brk).advancePC
      else if !decide (growBytes ≤ s.physMemAvail) then
        s.setStatus .OutOfMemory
      else
        let mem := s.mem.mapZero (BitVec.ofNat 64 oldPage) growBytes
        ((((s.setBrk addr).setMem mem).setPhysMemAvail (s.physMemAvail - growBytes)).writeReg64
          Reg.x0 addr).advancePC

end Arm64


