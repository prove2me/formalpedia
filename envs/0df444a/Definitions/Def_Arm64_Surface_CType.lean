-- Prove2me | Definitions.Def_Arm64_Surface_CType
-- name    : Arm64_Surface_CType
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T16:26:55.594805+00:00
-- url     : https://prove2.me/theorems/7ce8c043-daf2-4ba6-8289-fdb60881305e
-- title:
--   Arm64.Trusted.Surface.CType — semantic C types for AArch64 function contracts (without the c_type_spec command)
-- statement:
--   DeepMind's vocabulary of semantic C types for contracts of AArch64 functions called with the C calling convention, from the module [Arm64/Trusted/Surface/CType.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Surface/CType.lean) of google-deepmind/code-verification (Apache License 2.0), published with its Lean namespace (`Arm64.CType`) and names unchanged. A semantic type `SemType M` says how a C value of a given type is represented in registers and owned memory: for example `SizeT`, `MutSlice8` (a pointer and a length owning that many bytes read-write), `ShrSlice8`, `UninitSlot`. Contracts written with these types are ordinary `Spec` values of the published bundle `Arm64_Spec_Hoare`.
--
--   The bundle is the upstream module up to the heading "The `c_type_spec` Command": that command and its helpers are metaprogramming, which prove2.me does not accept, so a contract written with it upstream is published elsewhere as the `Spec` term it elaborates to (see the bundle `Musl_StringContracts`). The module's import of the DSL module `Arm64.Trusted.Surface.Abi` is replaced by the two published bundles it imports, `Arm64_Spec_Hoare` and `Arm64_Spec_RustAbi`, and `import Lean` is dropped. The "MODIFIED for prove2.me" notice after the license header states these changes; the module docstring is upstream's and still describes the command.
-- source:
--   Google DeepMind, code-verification (arm64-semantics), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Surface/CType.lean up to the c_type_spec command, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Surface/CType.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Surface/CType.lean`):
the `c_type_spec` command (everything from the heading "The `c_type_spec` Command" to the end:
syntax categories, macro_rules and their `meta` helpers) is removed, since prove2.me rejects
metaprogramming; `public import Lean` is dropped; the import of `Arm64.Trusted.Surface.Abi` (a DSL
module) is replaced by the two published modules it imports, `Definitions.Def_Arm64_Spec_Hoare` and
`Definitions.Def_Arm64_Spec_RustAbi`. The definitions are unchanged. A contract written with
`c_type_spec` upstream is published as the `Spec` term it elaborates to.
-/

module

public import Definitions.Def_Arm64_Spec_Hoare
public import Definitions.Def_Arm64_Spec_RustAbi

/-!
# Semantic C Type Judgements

Defines `SemType` and the `c_type_spec` surface command for ownership-typed C function contracts
with categorized caveats. Every C parameter and return value is assigned a semantic type
`T : SemType M` together with an ownership mode (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`,
or `Val`). Any pure precondition beyond argument well-formedness must be tagged as
`caveat [TAG] "why" : P` with `TAG` in `{API_RESTRICTION, CALLER_TYPESTATE, C_ARITH_BOUND, PARTIAL_SPEC}`;
raw `requires_cond`, `requires_pure`, `guard`, and `preserves` clauses are rejected.

`c_type_spec f ...` elaborates via `lowerParam` to an ordinary `c_spec f ...` (`f : Spec α`) plus a
metadata record `f.cTypeInfo : CTypeSpecInfo` used by `#c_type_report` and `tools/spec-review`.

| Clause | Precondition adds | Postcondition adds |
| :--- | :--- | :--- |
| `c_arg x : Own T m` (consumed) | `⌜T.pureWf x m⌝ ∗ T.interp x m` | - |
| `c_arg x : ShrRef T m` | `⌜T.pureWf x m⌝ ∗ T.interp x m` | `T.interp x m` |
| `c_arg x : MutRef T m ⇝ m'` | `⌜T.pureWf x m⌝ ∗ T.interp x m` | `⌜T.pureWf x m'⌝ ∗ T.interp x m'` |
| `c_arg x : UninitSlot n ⇝ T m'` | `memRegion x n` | `⌜T.pureWf x m'⌝ ∗ T.interp x m'` |
| `c_arg x : OutPtr T m` | `memRegion x 8` | `outPtrPost T x m` |
| `c_arg x : Val T` | `⌜T.valWf x⌝` | - |
| `c_ret : Own T m` (named `(ret : ..)` header) | - | `⌜T.pureWf ret m⌝ ∗ T.interp ret m` |
| `c_ret : ShrRef T m` / `MutRef T m` | - | `⌜T.pureWf ret m⌝` (footprint stays in parent `c_arg` / `c_env`) |
| `c_ret : Val T` | - | `⌜T.valWf ret⌝` |
| `caveat [TAG] "why" : P` | `⌜P⌝` | - |
| `c_env R` / `c_env R ⇝ R'` (allocator pool, globals) | `R` | `R` / `R'` |
| `c_exists (x : X)` | - | wraps the typed/`ensures` postcondition in `∃∗ x : X, ...` |
| `c_stack n` (callee stack budget) | `stackFrameAt s0.sp n` | `stackFrameAt sf.sp n` |
| `requires R` (untyped, flagged in metadata) | `R` | - |

Also forwarded to `c_spec` unchanged: `ensures`, `ensures_pure`, `returns`, `on_panic`, `oom_when`,
`on_oom`, `stack`, `stack16`, `stack32`, `let`, and `load_addr`. Every named register binder must
have a matching `c_arg` clause.

Separating conjunction between spatial argument footprints implies distinct pointer arguments do
not alias (for example, a `ShrRef CStr` source is disjoint from a `MutRef` destination buffer).
-/

public section

namespace Arm64.CType

@[expose] section

open Arm64

/-! ## Semantic Types and Caveat Metadata -/

/-- A semantic C type: canonical representation predicate `interp v m` (pointer or scalar register
    value `v` representing logical model `m`) paired with a pure well-formedness invariant `pureWf`
    required of every typed argument or return of this type. -/
structure SemType (M : Type) where
  /-- C-level type name shown to auditors (e.g. `"struct dynbuf"`). -/
  tyName : String
  /-- Spatial footprint of a value `v` representing model `m`. -/
  interp : BitVec 64 → M → SepProp
  /-- Pure invariant (e.g. `dynbufValid`) on register value/pointer `v : BitVec 64` (arg 1) and
      logical model `m : M` (arg 2). For value-only types used with `Val T`, arg 1 is unused
      (`0#64`) and arg 2 is the register value `x : M` itself. -/
  pureWf : BitVec 64 → M → Prop := fun _ _ => True

/-- Well-formedness of a scalar value of a value type (`Val T`): the register value `x : M` is
    passed as the model argument (arg 2) of `T.pureWf`, with dummy pointer `0#64` as arg 1. -/
@[reducible] def SemType.valWf {M : Type} (T : SemType M) (x : M) : Prop :=
  T.pureWf 0#64 x

/-- The four caveat categories of a `c_type_spec`. -/
inductive CaveatKind where
  /-- Genuine C API precondition: violating it is UB even with well-typed arguments. -/
  | apiRestriction
  /-- Lifecycle / protocol state restriction on a handle. -/
  | callerTypestate
  /-- C integer width / overflow bound. -/
  | cArithBound
  /-- Verification scope limitation: the C function accepts more, the proof covers less. -/
  | partialSpec
  deriving Repr, Inhabited, BEq

/-- Surface tag of a caveat kind (`API_RESTRICTION`, ...). -/
def CaveatKind.tag : CaveatKind → String
  | .apiRestriction => "API_RESTRICTION"
  | .callerTypestate => "CALLER_TYPESTATE"
  | .cArithBound => "C_ARITH_BOUND"
  | .partialSpec => "PARTIAL_SPEC"

/-- One tagged caveat: category, human explanation, and source text of the proposition. -/
structure CaveatClause where
  kind : CaveatKind
  desc : String
  prop : String
  deriving Repr, Inhabited

/-- Metadata of one typed parameter or return value (`mode` ∈ `Own`, `ShrRef`, `MutRef`,
    `UninitSlot`, `OutPtr`, `Val`; `ty` is the source text of the semantic type). -/
structure CParamInfo where
  name : String
  mode : String
  ty : String
  deriving Repr, Inhabited

/-- Structured metadata emitted by `c_type_spec f` as `f.cTypeInfo`. -/
structure CTypeSpecInfo where
  spec : String
  params : List CParamInfo
  ret : Option CParamInfo
  caveats : List CaveatClause
  env : List String
  untypedRequires : List String
  deriving Repr, Inhabited

/-! ## Value Types and Spatial Scalar Cells -/

/-- Unconstrained register scalar of C type `name` (empty spatial footprint; valid only with `Val`). -/
def scalarTy (w : Nat) (name : String) : SemType (BitVec w) :=
  { tyName := name, interp := fun _ _ => emp, pureWf := fun _ _ => True }

abbrev U8 : SemType (BitVec 8) := scalarTy 8 "uint8_t"
abbrev I8 : SemType (BitVec 8) := scalarTy 8 "int8_t"
abbrev U16 : SemType (BitVec 16) := scalarTy 16 "uint16_t"
abbrev I16 : SemType (BitVec 16) := scalarTy 16 "int16_t"
abbrev U32 : SemType (BitVec 32) := scalarTy 32 "uint32_t"
abbrev U64 : SemType (BitVec 64) := scalarTy 64 "uint64_t"
abbrev I32 : SemType (BitVec 32) := scalarTy 32 "int"
abbrev I64 : SemType (BitVec 64) := scalarTy 64 "int64_t"
abbrev SizeT : SemType (BitVec 64) := scalarTy 64 "size_t"
abbrev SSizeT : SemType (BitVec 64) := scalarTy 64 "ssize_t"
abbrev PtrdiffT : SemType (BitVec 64) := scalarTy 64 "ptrdiff_t"

/-- Spatial 1-byte scalar cell `p ↦₈ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U8Cell : SemType (BitVec 8) :=
  { tyName := "uint8_t", interp := fun p v => p ↦₈ v, pureWf := fun _ _ => True }
def I8Cell : SemType (BitVec 8) :=
  { tyName := "int8_t", interp := fun p v => p ↦₈ v, pureWf := fun _ _ => True }

/-- Spatial 2-byte scalar cell `p ↦₁₆ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U16Cell : SemType (BitVec 16) :=
  { tyName := "uint16_t", interp := fun p v => p ↦₁₆ v, pureWf := fun _ _ => True }
def I16Cell : SemType (BitVec 16) :=
  { tyName := "int16_t", interp := fun p v => p ↦₁₆ v, pureWf := fun _ _ => True }

/-- Spatial 4-byte scalar cell `p ↦₃₂ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U32Cell : SemType (BitVec 32) :=
  { tyName := "uint32_t", interp := fun p v => p ↦₃₂ v, pureWf := fun _ _ => True }
def I32Cell : SemType (BitVec 32) :=
  { tyName := "int", interp := fun p v => p ↦₃₂ v, pureWf := fun _ _ => True }

/-- Spatial 8-byte scalar cell `p ↦₆₄ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U64Cell : SemType (BitVec 64) :=
  { tyName := "uint64_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def I64Cell : SemType (BitVec 64) :=
  { tyName := "int64_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def SizeTCell : SemType (BitVec 64) :=
  { tyName := "size_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def SSizeTCell : SemType (BitVec 64) :=
  { tyName := "ssize_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def PtrdiffTCell : SemType (BitVec 64) :=
  { tyName := "ptrdiff_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }

/-- Status/return code drawn from the listed values. -/
def StatusCode {w : Nat} (codes : List (BitVec w)) : SemType (BitVec w) :=
  { tyName := "status code", interp := fun _ _ => emp, pureWf := fun _ r => r ∈ codes }

/-- Length register coupled to a byte-slice model `bs`: `n.toNat = bs.length`. -/
def SliceLen {w : Nat} (bs : List (BitVec 8)) : SemType (BitVec w) :=
  { tyName := "size_t (slice length)", interp := fun _ _ => emp,
    pureWf := fun _ n => n.toNat = bs.length }

/-! ## Pointer, Buffer, and String Types -/

/-- Nullable pointer: `none` corresponds to `NULL`, `some m` to a `T` at a non-null address. -/
def OptOwn {M : Type} (T : SemType M) : SemType (Option M) :=
  { tyName := T.tyName ++ " (nullable)",
    interp := fun p om => match om with
      | none => ⌜p = 0#64⌝
      | some m => T.interp p m,
    pureWf := fun p om => match om with
      | none => True
      | some m => p ≠ 0#64 ∧ T.pureWf p m }

/-- Byte buffer `p ↦ₛ bs` (read-write points-to; pair with `SliceLen bs` for the length). -/
def Bytes : SemType (List (BitVec 8)) :=
  { tyName := "uint8_t[]", interp := fun p bs => p ↦ₛ bs, pureWf := fun _ _ => True }

/-- Shared byte slice (`const uint8_t *p` with `len`): use as `ShrRef ShrSlice8 bs`. -/
abbrev ShrSlice8 : SemType (List (BitVec 8)) := Bytes
/-- Mutable byte slice (`uint8_t *p` with `len`): use as `MutRef MutSlice8 bs ⇝ bs'`. -/
abbrev MutSlice8 : SemType (List (BitVec 8)) := Bytes

/-- NUL-terminated C string: `p ↦ₛ (bs ++ [0])` with no interior NUL. -/
def CStr : SemType (List (BitVec 8)) :=
  { tyName := "char * (NUL-terminated)", interp := fun p bs => p ↦ₛ (bs ++ [0#8]),
    pureWf := fun _ bs => 0#8 ∉ bs }

/-- Nullable C string. -/
abbrev OptCStr : SemType (Option (List (BitVec 8))) := OptOwn CStr

/-- Postcondition of an output pointer `T **out`: the slot now holds some `v` representing `m`. -/
def outPtrPost {M : Type} (T : SemType M) (p : BitVec 64) (m : M) : SepProp :=
  ∃∗ v : BitVec 64, ⌜T.pureWf v m⌝ ∗ (p ↦₆₄ v) ∗ T.interp v m

/-- Fallible output-pointer payload `OutPtrOnOk T ok`: behaves as `T` when `ok` holds, and has
    empty spatial footprint and trivial `pureWf` when `¬ ok`. Paired with `OutPtr`:
    `c_arg out : OutPtr (OutPtrOnOk T (ret = 0#32)) m` requires `memRegion out 8` and yields
    `outPtrPost T out m` on success (`ret = 0#32`) and `out ↦₆₄ v` on error. -/
def OutPtrOnOk {M : Type} (T : SemType M) (ok : Prop) [Decidable ok] : SemType M :=
  { tyName := T.tyName ++ " (on ok)",
    interp := fun v m => if ok then T.interp v m else emp,
    pureWf := fun v m => if ok then T.pureWf v m else True }

/-- Optional 8-byte output-pointer slot `OptOutPtr T`: `none` is an uninitialized 8-byte slot
    `memRegion p 8`; `some m` is an initialized output slot `outPtrPost T p m`. Pair with
    `MutRef (OptOutPtr T) none ⇝ (if ret = 0#32 then some m else none)` or `UninitSlot 8`. -/
def OptOutPtr {M : Type} (T : SemType M) : SemType (Option M) :=
  { tyName := T.tyName ++ " * (out-slot)",
    interp := fun p om => match om with
      | none => memRegion p 8
      | some m => outPtrPost T p m,
    pureWf := fun _ _ => True }

/-- Conditionally-owned pointer `CondOwn T`: `some m` holds full ownership `T.interp p m` with
    `T.pureWf p m`; `none` means ownership was consumed/transferred (`emp`, without constraining
    the register value `p`). Pair with `MutRef` for fallible ownership transfer or `realloc`-style
    consumption: `c_arg p : MutRef (CondOwn T) (some m) ⇝ (if ok then none else some m)`. -/
def CondOwn {M : Type} (T : SemType M) : SemType (Option M) :=
  { tyName := T.tyName ++ " (cond-own)",
    interp := fun p om => match om with
      | none => emp
      | some m => T.interp p m,
    pureWf := fun p om => match om with
      | none => True
      | some m => T.pureWf p m }

/-- Borrowed interior pointer `InteriorPtr tyName` whose spatial footprint remains inside a
    borrowed parent container: `interp` is `emp` and `pureWf p target` asserts `p = target`.
    Use with `c_ret : ShrRef (InteriorPtr "const T *") targetAddr` (or `MutRef`). -/
def InteriorPtr (tyName : String) : SemType (BitVec 64) :=
  { tyName := tyName, interp := fun _ _ => emp, pureWf := fun p target => p = target }

end

end Arm64.CType


