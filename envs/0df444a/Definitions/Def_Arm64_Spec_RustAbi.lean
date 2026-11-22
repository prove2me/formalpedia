-- Prove2me | Definitions.Def_Arm64_Spec_RustAbi
-- name    : Arm64_Spec_RustAbi
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:13:50.562597+00:00
-- url     : https://prove2.me/theorems/e8de9fe6-3946-46e6-9306-57f774159c80
-- title:
--   Arm64.Trusted.Spec.RustAbi — Rust ABI Option and Result Encoders
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/RustAbi.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/RustAbi.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/RustAbi.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/RustAbi.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/RustAbi.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Spec_SepLogic

/-!
# Rust ABI `Option` and `Result` Encoders

Typed return-value encodings (`RetEnc`) and in-memory predicates for common `Option<T>` and
`Result<T, E>` layouts under `rustc 1.98.1` (`aarch64-unknown-linux-gnu`, `extern "Rust"` ABI).
Each encoder corresponds to one concrete LLVM return type emitted by `rustc 1.98.1` and constrains
only the bits defined by that ABI type (for example, `{ i1, i8 }` defines `W0[0]` and `W1[7:0]`
only, leaving the payload register unconstrained on `none` or unit-error returns). Rust layouts are
unstable across compiler versions; a layout change renders affected `subroutineOk` theorems
unprovable against the compiled binary.
-/

@[expose] public section

namespace Arm64.RustAbi

/-- A typed Rust return-value encoding: `holds sf v` says the exit state `sf` returns the Rust
    value represented by `v : α` under the Rust AArch64 ABI. -/
structure RetEnc (α : Type) where
  holds : State → α → Prop

/-! ## `ScalarPair` `Option<intN>` (tag register + payload register)

`rustc` lowers `Option<uN>` / `Option<iN>` to the LLVM aggregate `{ iN, iN }` (tag widened to the
payload width; `{ i1, i8 }` for 8-bit payloads), returned in `(x0, x1)` per AAPCS64.
`0` = `None`, `1` = `Some`. -/

/-- `Option<u64>` / `Option<i64>` / `Option<usize>`: LLVM `{ i64, i64 }`.
    `none ↔ X0 = 0` (X1 unconstrained), `some v ↔ X0 = 1 ∧ X1 = v`. -/
def optionU64 : RetEnc (Option (BitVec 64)) where
  holds sf
    | none => sf.readReg64 .x0 = 0#64
    | some v => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = v

/-- `Option<u32>` / `Option<i32>`: LLVM `{ i32, i32 }` (`W0` tag, `W1` payload; upper halves
    unspecified). -/
def optionU32 : RetEnc (Option (BitVec 32)) where
  holds sf
    | none => sf.readReg32 .x0 = 0#32
    | some v => sf.readReg32 .x0 = 1#32 ∧ sf.readReg32 .x1 = v

/-- `Option<u16>` / `Option<i16>`: LLVM `{ i16, i16 }` (`W0[15:0]` tag, `W1[15:0]` payload). -/
def optionU16 : RetEnc (Option (BitVec 16)) where
  holds sf
    | none => (sf.readReg32 .x0).truncate 16 = 0#16
    | some v => (sf.readReg32 .x0).truncate 16 = 1#16 ∧ (sf.readReg32 .x1).truncate 16 = v

/-- `Option<u8>` / `Option<i8>`: LLVM `{ i1, i8 }`. Only `W0[0]` (tag) and `W1[7:0]` (payload)
    are defined. -/
def optionU8 : RetEnc (Option (BitVec 8)) where
  holds sf
    | none => (sf.readReg32 .x0).truncate 1 = 0#1
    | some v => (sf.readReg32 .x0).truncate 1 = 1#1 ∧ (sf.readReg32 .x1).truncate 8 = v

/-! ## Niche-encoded `Option` in one register -/

/-- `Option<&T>` / `Option<&mut T>` / `Option<Box<T>>` / `Option<NonNull<T>>` /
    `Option<NonZeroU64>`: LLVM `ptr` / `i64`, null niche. `none ↔ X0 = 0`,
    `some p ↔ p ≠ 0 ∧ X0 = p` (a `some 0` value is not representable). -/
def optionNonNull64 : RetEnc (Option (BitVec 64)) where
  holds sf
    | none => sf.readReg64 .x0 = 0#64
    | some p => p ≠ 0#64 ∧ sf.readReg64 .x0 = p

/-- `Option<NonZeroU32>`: LLVM `i32`, zero niche in `W0`. -/
def optionNonZero32 : RetEnc (Option (BitVec 32)) where
  holds sf
    | none => sf.readReg32 .x0 = 0#32
    | some v => v ≠ 0#32 ∧ sf.readReg32 .x0 = v

/-- `Option<&[T]>` / `Option<&str>`: LLVM `{ ptr, i64 }`, null niche in the data pointer.
    `none ↔ X0 = 0` (X1 unconstrained), `some (p, n) ↔ p ≠ 0 ∧ X0 = p ∧ X1 = n`. -/
def optionSlice : RetEnc (Option (BitVec 64 × BitVec 64)) where
  holds sf
    | none => sf.readReg64 .x0 = 0#64
    | some (p, n) => p ≠ 0#64 ∧ sf.readReg64 .x0 = p ∧ sf.readReg64 .x1 = n

/-! ## `ScalarPair` `Result<T, E>` (`0` = `Ok`, `1` = `Err`)

Only shapes whose LLVM return type is a two-scalar aggregate are listed. `Result<u64, E>` with a
1- to 4-byte `E` (e.g. `Result<u64, u32>`, `Result<u64, MyEnum>`) is returned through `x8` (`sret`)
and is not covered; nor is `Result<(), FieldlessEnum>`, whose `Ok` niche value (`0xff` under
`1.98.1`) is a compiler choice. -/

/-- `Result<u64, u64>` (also `usize`/`i64`): LLVM `{ i64, i64 }`. -/
def resultU64 : RetEnc (Except (BitVec 64) (BitVec 64)) where
  holds sf
    | .ok v => sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v
    | .error e => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = e

/-- `Result<u64, ()>` (also `usize`/`i64`): LLVM `{ i64, i64 }`; X1 unconstrained on `Err`. -/
def resultU64Unit : RetEnc (Except Unit (BitVec 64)) where
  holds sf
    | .ok v => sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v
    | .error () => sf.readReg64 .x0 = 1#64

/-- `Result<u32, u32>` (also `i32`): LLVM `{ i32, i32 }`. -/
def resultU32 : RetEnc (Except (BitVec 32) (BitVec 32)) where
  holds sf
    | .ok v => sf.readReg32 .x0 = 0#32 ∧ sf.readReg32 .x1 = v
    | .error e => sf.readReg32 .x0 = 1#32 ∧ sf.readReg32 .x1 = e

/-- `Result<(), u32>`: LLVM `{ i32, i32 }`; W1 unconstrained on `Ok`. -/
def resultUnitU32 : RetEnc (Except (BitVec 32) Unit) where
  holds sf
    | .ok () => sf.readReg32 .x0 = 0#32
    | .error e => sf.readReg32 .x0 = 1#32 ∧ sf.readReg32 .x1 = e

/-- `Result<u8, E>` where `E` is `u8`, `i8`, or a fieldless `#[repr(u8)]`/default enum with at
    most 256 variants (the payload byte is the discriminant): LLVM `{ i1, i8 }`. -/
def resultU8 : RetEnc (Except (BitVec 8) (BitVec 8)) where
  holds sf
    | .ok v => (sf.readReg32 .x0).truncate 1 = 0#1 ∧ (sf.readReg32 .x1).truncate 8 = v
    | .error e => (sf.readReg32 .x0).truncate 1 = 1#1 ∧ (sf.readReg32 .x1).truncate 8 = e

/-! ## In-memory `Option` (sret buffers and struct fields) -/

/-- `Option<T>` of size `size` at `p` where `T` (e.g. `String`, `Vec<U>`, a struct starting with a
    `Vec`) has a capacity niche at offset 0: `None` stores `usize::MAX` (`2^64 - 1`, `rustc 1.98.1`)
    at `p` and leaves the remaining `size - 8` bytes unspecified; `Some x` is `inner p x`. -/
def optionCapNicheAt {α : Type} (size : Nat) (inner : BitVec 64 → α → SepProp)
    (p : BitVec 64) : Option α → SepProp
  | none => (p ↦₆₄ 0xffff_ffff_ffff_ffff#64) ∗ memRegion (p + 8#64) (size - 8)
  | some x => inner p x

/-- `Option<T>` at `p` with an explicit 8-byte tag word at `p` (`T` 8-byte aligned without a niche,
    e.g. `Option<(u64, u64)>`, `Option<[u64; 3]>`): `None` stores `0` at `p` and leaves the
    `payloadSize` payload bytes at `p + 8` unspecified; `Some x` stores `1` and `inner (p + 8) x`. -/
def optionTagged64At {α : Type} (payloadSize : Nat) (inner : BitVec 64 → α → SepProp)
    (p : BitVec 64) : Option α → SepProp
  | none => (p ↦₆₄ 0#64) ∗ memRegion (p + 8#64) payloadSize
  | some x => (p ↦₆₄ 1#64) ∗ inner (p + 8#64) x

end Arm64.RustAbi


