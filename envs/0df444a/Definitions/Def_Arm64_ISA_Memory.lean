-- Prove2me | Definitions.Def_Arm64_ISA_Memory
-- name    : Arm64_ISA_Memory
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:02:42.150686+00:00
-- url     : https://prove2.me/theorems/54b089ac-3528-42ad-9211-52afcd3b5f8c
-- title:
--   Arm64.Trusted.ISA.Memory — ARM64 Byte-Addressable Little-Endian Virtual Memory
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/Memory.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Memory.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/Memory.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Memory.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/Memory.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also the constructor `Step.extern` renamed `Step.externHook` in comments (see below).
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Syntax

/-!
# ARM64 Byte-Addressable Little-Endian Virtual Memory (`Arm64.Memory`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: 64-bit byte-addressable virtual memory (`Memory`) mapping addresses
  to per-byte optional permissions and bytes (`cells : BitVec 64 → Option (Option Perm × BitVec 8)`),
  protection flags (`Perm`, `Perm.protNone`, `Perm.ro`, `Perm.rw`, `Perm.rx`, `canRead`, `canWrite`,
  `canExec`, `canMap`, `countPerm`, `countRw`), little-endian accessors (`read8`, `read16`, `read32`, `read64`, `read128`,
  `write8`, `write16`, `write32`, `write64`, `write128`, `readBytes`, `writeBytes`), and mapping
  helpers (`mapFresh`, `mapZero`, `unmapNonFrozen`, `setPermNonFrozen`, `zeroNonFrozen`).
- **When to read**: Use this header or `lean-sig outline Arm64/Trusted/ISA/Memory.lean` for API names;
  use `ProofLib/Memory.lean` and `Arm64/Trusted/Spec/SepLogic.lean` for reasoning about memory in proofs.

## Conservative Permissions, `Option Perm`, & W^X
`read*`/`write*` ignore permissions; `Arm64.execInst` checks `canRead`/`canWrite`/`canExec`
before every access and faults otherwise. Writes never alter permissions.
A byte's permission in `Memory` is `m.perm a : Option Perm`:
- `none` is **unmapped** (no VMA). Permissions are *conservative* (at most the real machine's):
  **"unmapped" (`none`) means "not known to be accessible", not "guaranteed to fault"**, so proofs
  must avoid unmapped bytes without deriving facts from unmappedness.
- `some p` is **mapped** (`(m.perm a).mapped = (m.perm a).isSome = true`) with Linux protection
  bits `p : Perm` (`r`, `w`, `x`). In particular, `some Perm.protNone` (`some ⟨false, false, false⟩`)
  is a mapped `PROT_NONE` page: reserved in the virtual address space (`canMap = false`, so `mmap`
  and `brk` never overlap it), inaccessible (`canRead = canWrite = canExec = false`), and not
  frozen (`frozen = false`).
- Executable memory is never writable (`canWrite` requires `w ∧ ¬x`, W^X), ensuring loaded
  instructions remain immutable across execution.
-/

@[expose] public section

namespace Arm64

/-- Linux protection bits (`PROT_READ`, `PROT_WRITE`, `PROT_EXEC`) and per-byte VM state of a
    mapped byte of virtual memory: readable (`r`), writable (`w`), executable (`x`), whether the
    byte is marked `lazyfree` via `madvise(..., MADV_FREE)` (`lazyFree`, asynchronously zeroable
    until dirtied by a store), and whether the byte belongs to an anonymous mapping (`anon`, `false`
    on file-backed `PT_LOAD` pages). -/
structure Perm where
  r : Bool
  w : Bool
  x : Bool
  lazyFree : Bool := false
  anon : Bool := true
  deriving DecidableEq, Repr, Inhabited

namespace Perm

/-- Mapped with `PROT_NONE` (`---`): reserved in the virtual address space, inaccessible to
    loads, stores, and instruction fetches (`r = w = x = false`), and not frozen (`frozen = false`). -/
def protNone : Perm := ⟨false, false, false, false, true⟩
/-- Read-only (`r--`). -/
def ro : Perm := ⟨true, false, false, false, true⟩
/-- Read-write (`rw-`). -/
def rw : Perm := ⟨true, true, false, false, true⟩
/-- Read-execute (`r-x`), for code. -/
def rx : Perm := ⟨true, false, true, false, true⟩

/-- Normalized 3-bit protection projection (`r`, `w`, `x`) with default `lazyFree = false` and
    `anon = true`. -/
def rwx (p : Perm) : Perm :=
  { r := p.r, w := p.w, x := p.x }

/-- The mapped byte is read-only or executable and not writable. Its contents and permission
    are *frozen*: nothing during execution may change them (see `Memory.KeepsFrozen`). -/
def frozen (p : Perm) : Bool := (p.r || p.x) && !p.w

end Perm

/-- An optional byte permission is mapped iff it is `some p` (`isSome`). -/
@[simp, reducible] def _root_.Option.mapped (p : Option Perm) : Bool := p.isSome

/-- An optional byte permission is readable iff it is `some q` with `q.r = true`. -/
@[simp, reducible] def _root_.Option.r (p : Option Perm) : Bool :=
  match p with
  | some q => q.r
  | none => false

/-- An optional byte permission is writable iff it is `some q` with `q.w = true`. -/
@[simp, reducible] def _root_.Option.w (p : Option Perm) : Bool :=
  match p with
  | some q => q.w
  | none => false

/-- An optional byte permission is executable iff it is `some q` with `q.x = true`. -/
@[simp, reducible] def _root_.Option.x (p : Option Perm) : Bool :=
  match p with
  | some q => q.x
  | none => false

/-- An optional byte permission is frozen iff it is `some q` with `q.frozen = true`. -/
@[simp, reducible] def _root_.Option.frozen (p : Option Perm) : Bool :=
  match p with
  | some q => q.frozen
  | none => false

/-- Byte-addressable 64-bit virtual memory: a partial map from addresses to an optional permission
    (`Option Perm`) and a byte (`BitVec 8`). `none` is an untouched address (unmapped, byte `0`).

    **Representation.** Lean core and `Std` provide no proof-friendly partial map over the full
    64-bit address space: `Std.TreeMap` / `Std.HashMap` are finite, computational structures whose
    reasoning principles are about insertion histories, not pointwise lookups. A total function
    into `Option` is the simplest faithful model and makes pointwise lemmas (read-over-write,
    permission-over-write) one-line case splits.

    **Interface.** Clients use the derived accessors `read8` (the byte, `0` if absent) and
    `perm` (`Option Perm`: `none` if unmapped, `some p` if mapped with protection `p`) together
    with the base lemmas of `ProofLib.Invariant` / `ProofLib.CoreLemmas` (`read8_write8`,
    `perm_write8`, `perm_mapFresh`, ...), never `cells` directly.

    **Writes to unmapped addresses.** `write8` stores `some (m.perm a, v)`, so a raw write to an
    unmapped address (`m.perm a = none`) creates `some (none, v)` with permission `none` (unmapped),
    never `some (some ⟨false, false, false⟩, v)`. This keeps `read8_write8` and `perm_write8`
    unconditional while reserving `some ⟨false, false, false⟩` (`some Perm.protNone`) exclusively
    for mapped `PROT_NONE` pages. -/
@[ext]
structure Memory where
  cells : BitVec 64 → Option (Option Perm × BitVec 8)

namespace Memory

/-- All-zero, unmapped initial memory: no cells. -/
def empty : Memory := ⟨fun _ => none⟩

/-- The default `Memory` is `empty`. -/
instance : Inhabited Memory := ⟨empty⟩

/-- The memory with byte `bytes a` and optional permission `perm a` at every address. -/
def ofFn (bytes : BitVec 64 → BitVec 8) (perm : BitVec 64 → Option Perm := fun _ => none) :
    Memory :=
  ⟨fun a => some (perm a, bytes a)⟩

/-- The raw optional cell permission at `addr` (including `lazyFree` and `anon` bits). -/
def rawPerm (m : Memory) (addr : BitVec 64) : Option Perm :=
  match m.cells addr with
  | some (p, _) => p
  | none => none

/-- The normalized 3-bit protection (`r`, `w`, `x`) of the byte at `addr` (`none` if unmapped,
    `some p.rwx` if mapped with `p`). Invariant under stores (`write8`) and `madvise`. -/
def perm (m : Memory) (addr : BitVec 64) : Option Perm :=
  match m.cells addr with
  | some (some p, _) => some p.rwx
  | _ => none

/-- Whether the byte at `addr` is mapped and marked `lazyfree` via `MADV_FREE`
    (so its contents may be asynchronously reclaimed to zero by Linux `7.3` until overwritten). -/
def isLazyFree (m : Memory) (addr : BitVec 64) : Bool :=
  match m.cells addr with
  | some (some p, _) => p.lazyFree
  | _ => false

/-- Whether the byte at `addr` is mapped as anonymous memory (`vma_is_anonymous` on Linux `7.3`;
    `false` on unmapped bytes and file-backed `PT_LOAD` pages). -/
def isAnon (m : Memory) (addr : BitVec 64) : Bool :=
  match m.cells addr with
  | some (some p, _) => p.anon
  | _ => false

/-- Protection + `lazyFree` projection at `addr` (`some Perm.rw` iff `m.perm addr = some Perm.rw`
    and `m.isLazyFree addr = false`). -/
def permNoLazy (m : Memory) (addr : BitVec 64) : Option Perm :=
  match m.cells addr with
  | some (some p, _) => some { r := p.r, w := p.w, x := p.x, lazyFree := p.lazyFree }
  | _ => none

/-- Read a single byte (`8` bits) at `addr` (`0` if unmapped). -/
def read8 (m : Memory) (addr : BitVec 64) : BitVec 8 :=
  match m.cells addr with
  | some (_, b) => b
  | none => 0#8

/-- Write a single byte (`8` bits) at `addr`. Normalized permissions (`m.perm`) and `m.isAnon` are
    unchanged; writing clears `lazyFree := false` (storing dirties the PTE on Linux `7.3`,
    cancelling lazy reclaim). -/
def write8 (m : Memory) (addr : BitVec 64) (val : BitVec 8) : Memory :=
  ⟨fun a =>
    if a = addr then
      let p' := match m.rawPerm addr with
        | some p => some { p with lazyFree := false }
        | none => none
      some (p', val)
    else
      m.cells a⟩

/-- Read a 16-bit halfword in little-endian byte order at `addr`. -/
def read16 (m : Memory) (addr : BitVec 64) : BitVec 16 :=
  let b0 := m.read8 (addr + 0#64)
  let b1 := m.read8 (addr + 1#64)
  b1 ++ b0

/-- Write a 16-bit halfword in little-endian byte order at `addr`. -/
def write16 (m : Memory) (addr : BitVec 64) (val : BitVec 16) : Memory :=
  let m := m.write8 (addr + 0#64) (val.extractLsb' 0 8)
  let m := m.write8 (addr + 1#64) (val.extractLsb' 8 8)
  m

/-- Read a 32-bit word in little-endian byte order at `addr`. -/
def read32 (m : Memory) (addr : BitVec 64) : BitVec 32 :=
  let b0 := m.read8 (addr + 0#64)
  let b1 := m.read8 (addr + 1#64)
  let b2 := m.read8 (addr + 2#64)
  let b3 := m.read8 (addr + 3#64)
  b3 ++ b2 ++ b1 ++ b0

/-- Write a 32-bit word in little-endian byte order at `addr`. -/
def write32 (m : Memory) (addr : BitVec 64) (val : BitVec 32) : Memory :=
  let m := m.write8 (addr + 0#64) (val.extractLsb' 0 8)
  let m := m.write8 (addr + 1#64) (val.extractLsb' 8 8)
  let m := m.write8 (addr + 2#64) (val.extractLsb' 16 8)
  let m := m.write8 (addr + 3#64) (val.extractLsb' 24 8)
  m

/-- Read a 64-bit doubleword in little-endian byte order at `addr`. -/
def read64 (m : Memory) (addr : BitVec 64) : BitVec 64 :=
  let b0 := m.read8 (addr + 0#64)
  let b1 := m.read8 (addr + 1#64)
  let b2 := m.read8 (addr + 2#64)
  let b3 := m.read8 (addr + 3#64)
  let b4 := m.read8 (addr + 4#64)
  let b5 := m.read8 (addr + 5#64)
  let b6 := m.read8 (addr + 6#64)
  let b7 := m.read8 (addr + 7#64)
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

/-- Write a 64-bit doubleword in little-endian byte order at `addr`. -/
def write64 (m : Memory) (addr : BitVec 64) (val : BitVec 64) : Memory :=
  let m := m.write8 (addr + 0#64) (val.extractLsb' 0 8)
  let m := m.write8 (addr + 1#64) (val.extractLsb' 8 8)
  let m := m.write8 (addr + 2#64) (val.extractLsb' 16 8)
  let m := m.write8 (addr + 3#64) (val.extractLsb' 24 8)
  let m := m.write8 (addr + 4#64) (val.extractLsb' 32 8)
  let m := m.write8 (addr + 5#64) (val.extractLsb' 40 8)
  let m := m.write8 (addr + 6#64) (val.extractLsb' 48 8)
  let m := m.write8 (addr + 7#64) (val.extractLsb' 56 8)
  m

/-- Read memory of `size` bytes (`B8`, `H16`, `W32`, `X64`), zero-extended or sign-extended to 64 bits. -/
def readSized (m : Memory) (size : MemWidth) (signed : Bool) (addr : BitVec 64) : BitVec 64 :=
  match size with
  | .B8  =>
    let b := m.read8 addr
    if signed then b.signExtend 64 else b.zeroExtend 64
  | .H16 =>
    let h := m.read16 addr
    if signed then h.signExtend 64 else h.zeroExtend 64
  | .W32 =>
    let w := m.read32 addr
    if signed then w.signExtend 64 else w.zeroExtend 64
  | .X64 =>
    m.read64 addr

/-- Write memory of `size` bytes (`B8`, `H16`, `W32`, `X64`) from a 64-bit value. -/
def writeSized (m : Memory) (size : MemWidth) (addr : BitVec 64) (val : BitVec 64) : Memory :=
  match size with
  | .B8  => m.write8 addr (val.truncate 8)
  | .H16 => m.write16 addr (val.truncate 16)
  | .W32 => m.write32 addr (val.truncate 32)
  | .X64 => m.write64 addr val

/-- Read a 128-bit quadword in little-endian byte order at `addr`. -/
def read128 (m : Memory) (addr : BitVec 64) : BitVec 128 :=
  let lo := m.read64 addr
  let hi := m.read64 (addr + 8#64)
  hi ++ lo

/-- Write a 128-bit quadword in little-endian byte order at `addr`. -/
def write128 (m : Memory) (addr : BitVec 64) (val : BitVec 128) : Memory :=
  let m := m.write64 addr (val.extractLsb' 0 64)
  let m := m.write64 (addr + 8#64) (val.extractLsb' 64 64)
  m

/-- Read memory of `SimdMemSize` (`B8`, `H16`, `S32`, `D64`, `Q128`), zero-extended to 128 bits. -/
def readSimdSized (m : Memory) (size : SimdMemSize) (addr : BitVec 64) : BitVec 128 :=
  match size with
  | .B8   => (m.read8 addr).zeroExtend 128
  | .H16  => (m.read16 addr).zeroExtend 128
  | .S32  => (m.read32 addr).zeroExtend 128
  | .D64  => (m.read64 addr).zeroExtend 128
  | .Q128 => m.read128 addr

/-- Write memory of `SimdMemSize` (`B8`, `H16`, `S32`, `D64`, `Q128`) from a 128-bit SIMD register value. -/
def writeSimdSized (m : Memory) (size : SimdMemSize) (addr : BitVec 64) (val : BitVec 128) : Memory :=
  match size with
  | .B8   => m.write8 addr (val.truncate 8)
  | .H16  => m.write16 addr (val.truncate 16)
  | .S32  => m.write32 addr (val.truncate 32)
  | .D64  => m.write64 addr (val.truncate 64)
  | .Q128 => m.write128 addr val

/-- Read `count` contiguous bytes starting at `base`
    (`[m.read8 (base + 0), m.read8 (base + 1), ..., m.read8 (base + (count - 1))]`). -/
def readBytes (m : Memory) (base : BitVec 64) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => m.read8 base :: m.readBytes (base + 1#64) n

/-- Write a contiguous list of bytes starting at `base`, so that byte `i` lands at `base + i`.
    Used to load statically initialized data (e.g. an exported ELF `.rodata` image) into memory. -/
def writeBytes (m : Memory) (base : BitVec 64) : List (BitVec 8) → Memory
  | [] => m
  | b :: rest => (m.write8 base b).writeBytes (base + 1#64) rest

/-! ## Permissions -/

/-- Every byte of `[addr, addr + n)` (wrapping modulo `2^64`) has an optional permission satisfying `p`. -/
def allPerm (m : Memory) (p : Option Perm → Bool) (addr : BitVec 64) : Nat → Bool
  | 0 => true
  | n + 1 => p (m.perm addr) && m.allPerm p (addr + 1#64) n

/-- Every byte of `[addr, addr + n)` (wrapping modulo `2^64`) has `isLazyFree = false`. -/
def allNoLazyFree (m : Memory) (addr : BitVec 64) : Nat → Bool
  | 0 => true
  | n + 1 => !m.isLazyFree addr && m.allNoLazyFree (addr + 1#64) n

/-- Every byte of `[addr, addr + n)` (wrapping modulo `2^64`) is mapped anonymous (`isAnon = true`). -/
def allAnon (m : Memory) (addr : BitVec 64) : Nat → Bool
  | 0 => true
  | n + 1 => m.isAnon addr && m.allAnon (addr + 1#64) n

/-- `[addr, addr + n)` is deterministically readable (`r = true` and not marked `lazyFree` via
    `MADV_FREE`). Reading an unwritten `lazyFree` byte fails closed because Linux `7.3` may
    asynchronously reclaim the page to zero between loads (`mm/rmap.c` `ttu_anon_lazyfree_folio`). -/
def canRead (m : Memory) (addr : BitVec 64) (n : Nat) : Bool :=
  m.allPerm (·.r) addr n && m.allNoLazyFree addr n

/-- `[addr, addr + n)` is writable: `w` and **not** `x`. Stores to executable memory always
    fault, so the code of a loaded program never changes. -/
def canWrite (m : Memory) (addr : BitVec 64) (n : Nat) : Bool :=
  m.allPerm (fun p => p.w && !p.x) addr n

/-- `[addr, addr + n)` is executable. -/
def canExec (m : Memory) (addr : BitVec 64) (n : Nat) : Bool :=
  m.allPerm (·.x) addr n

/-- `[addr, addr + n)` is unmapped (`!(m.perm a).mapped` for every byte). -/
def canMap (m : Memory) (addr : BitVec 64) (n : Nat) : Bool :=
  m.allPerm (fun p => !p.mapped) addr n

/-- Number of bytes in `[addr, addr + n)` (wrapping modulo `2^64`) whose optional permission
    satisfies `p`. -/
def countPerm (m : Memory) (p : Option Perm → Bool) (addr : BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => (if p (m.perm addr) then 1 else 0) + m.countPerm p (addr + 1#64) n

/-- Number of bytes in `[addr, addr + n)` mapped with `Perm.rw` (`m.perm a == some Perm.rw`). -/
def countRw (m : Memory) (addr : BitVec 64) (n : Nat) : Nat :=
  m.countPerm (· == some Perm.rw) addr n

/-- Byte `a` is frozen in `m`: mapped read-only or executable and not writable (`Option.frozen`). -/
def Frozen (m : Memory) (a : BitVec 64) : Prop := (m.perm a).frozen = true

/-- `m'` keeps every byte that is frozen in `m`: same contents, same permission, same `lazyFree`
    bit, and same anonymous-mapping bit (`isAnon`). Every `Step` does this (instructions only store
    to `canWrite` bytes; extern hooks must, see `Step.externHook`), so code and read-only data stay
    loaded throughout execution. -/
def KeepsFrozen (m m' : Memory) : Prop :=
  ∀ a, m.Frozen a →
    m'.read8 a = m.read8 a ∧ m'.perm a = m.perm a ∧
    m'.isLazyFree a = m.isLazyFree a ∧ m'.isAnon a = m.isAnon a

/-- Map the currently unmapped bytes of `[base, base + len)` with permission `p`; mapped
    bytes are unchanged. Contents are unchanged (unspecified: whatever `read8` returned before,
    `0` for an address without a cell).

    This is a conservative simplification of the kernel, which maps whole pages: here nothing
    mapped is ever replaced, so the frozen bytes of the program stay intact. -/
def mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) : Memory :=
  ⟨fun a =>
    if (a - base).toNat < len && !(m.perm a).mapped then some (some p, m.read8 a) else m.cells a⟩

/-- Map the currently unmapped bytes of `[base, base + len)` read-write and zero-filled;
    mapped bytes are unchanged. Used for the fresh pages of `brk` growth and anonymous `mmap`,
    which Linux zero-fills. Never touches frozen bytes. -/
def mapZero (m : Memory) (base : BitVec 64) (len : Nat) : Memory :=
  ⟨fun a =>
    if (a - base).toNat < len && !(m.perm a).mapped then some (some Perm.rw, 0#8) else m.cells a⟩

end Memory

/-- Number of bytes accessed by a SIMD load or store of size `sz`. -/
@[simp, reducible] def SimdMemSize.bytes : SimdMemSize → Nat
  | .B8 => 1 | .H16 => 2 | .S32 => 4 | .D64 => 8 | .Q128 => 16

end Arm64


