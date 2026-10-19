-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
-- name    : MIPRE_TM_CookLevin_FamilyFml
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:05:47.499335+00:00
-- url     : https://prove2.me/theorems/3f592f0c-df84-4a9b-9eca-644f56de5b64
-- title:
--   Definitions of FamilyFml: The clause families as formulas For each family predicate of `Families.lean` and `Window.lean`, the formula computing…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.FamilyFml` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The clause families as formulas. For each family predicate of `Families.lean` and `Window.lean`, the formula computing it on a candidate of field formulas (`CandF`: three `FieldsF` and three sign formulas), with its exact semantics (`eval_startF`, …, `eval_windowF`) and its input bound. The fixed input tapes enter through value formulas (`cellValF` for a listed string, `unaryValF` for the unary time bound), tied to `fixed` by `TapeSpec`; the free tapes through the list of their indices (`FreeSpec`) (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (75): `MIPRE.TM.CookLevin.Desc.CandF` (A candidate of formulas: three field records and three sign formulas.); `MIPRE.TM.CookLevin.Desc.CandF.InputsLt` (The candidate reads only inputs below `n`.); `MIPRE.TM.CookLevin.Desc.CandF.Lengths` (The three records have the field lengths.); `MIPRE.TM.CookLevin.Desc.FieldsF.InputsLt` (The field formulas read only inputs below `n`.); `MIPRE.TM.CookLevin.Desc.FreeSpec` (The tapes `fixed j = none` are the indices `frees`.); `MIPRE.TM.CookLevin.Desc.LDesc` (A literal spec as data.); `MIPRE.TM.CookLevin.Desc.LitSpec.toN` (The descriptor of a spec.); `MIPRE.TM.CookLevin.Desc.NTpl` (A template as data.); `MIPRE.TM.CookLevin.Desc.TapeSpec` (The entries `(j, vf)` of `tabs` are the fixed tapes `fixed j = some x`, with `vf` computing `v = cellCode x S p` on the record `A`.); `MIPRE.TM.CookLevin.Desc.Tpl.toN` (The descriptor of a template.); `MIPRE.TM.CookLevin.Desc.WDesc` (A window variable as data: the kind (one-hot over `cellPre`, `headPre`, `cellPost`, `headPost`, `statePre`, `statePost`, `emitOne`,…); `MIPRE.TM.CookLevin.Desc.auxEqF` (`auxEq`.); `MIPRE.TM.CookLevin.Desc.auxMatchN` (`SpecMatch` for a gate spec, with the gate index as bits.); `MIPRE.TM.CookLevin.Desc.badDesc` (The descriptor of nothing: no kind.); `MIPRE.TM.CookLevin.Desc.bdryCellF` (`BdryCell`.); `MIPRE.TM.CookLevin.Desc.bdryF` (`Bdry S p`.); `MIPRE.TM.CookLevin.Desc.bdryHeadF` (`BdryHead`.); `MIPRE.TM.CookLevin.Desc.bdryPredF` (`BdryPred`.); and 34 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_oneHot`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.FamilyFml` (`MIPRE/TM/CookLevin/FamilyFml.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/FamilyFml.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FamilyFml.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window

/-!
# The clause families as formulas

For each family predicate of `Families.lean` and `Window.lean`, the formula computing it on a
candidate of field formulas (`CandF`: three `FieldsF` and three sign formulas), with its
exact semantics (`eval_startF`, …, `eval_windowF`) and its input bound. The fixed input
tapes enter through value formulas (`cellValF` for a listed string, `unaryValF` for the
unary time bound), tied to `fixed` by `TapeSpec`; the free tapes through the list of their
indices (`FreeSpec`) (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## Helpers -/

/-! ## Input bounds of the field formulas -/

/-- The field formulas read only inputs below `n`. -/
structure FieldsF.InputsLt (n : ℕ) (A : FieldsF) : Prop where
  flag : A.flag.InputsLt n
  tag : ∀ f ∈ A.tag, f.InputsLt n
  t : ∀ f ∈ A.t, f.InputsLt n
  d : ∀ f ∈ A.d, f.InputsLt n
  p : ∀ f ∈ A.p, f.InputsLt n
  v : ∀ f ∈ A.v, f.InputsLt n
  q : ∀ f ∈ A.q, f.InputsLt n
  js : ∀ k, ∀ f ∈ A.js k, f.InputsLt n
  g : ∀ f ∈ A.g, f.InputsLt n
  ansOk : A.ansOk.InputsLt n

section LitInputs

variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn

end LitInputs

section KindInputs

variable {e G n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA

end KindInputs

/-! ## Candidates of formulas -/

/-- A candidate of formulas: three field records and three sign formulas. -/
structure CandF where
  A₁ : FieldsF
  σ₁ : Fml
  A₂ : FieldsF
  σ₂ : Fml
  A₃ : FieldsF
  σ₃ : Fml

/-- The candidate a candidate of formulas evaluates to. -/
def evalCand (C : CandF) (x : ℕ → Bool) : Cand :=
  ⟨evalFields C.A₁ x, C.σ₁.eval x, evalFields C.A₂ x, C.σ₂.eval x, evalFields C.A₃ x, C.σ₃.eval x⟩

/-- The three records have the field lengths. -/
structure CandF.Lengths (e G : ℕ) (C : CandF) : Prop where
  A₁ : C.A₁.Lengths e G
  A₂ : C.A₂.Lengths e G
  A₃ : C.A₃.Lengths e G

/-- The candidate reads only inputs below `n`. -/
structure CandF.InputsLt (n : ℕ) (C : CandF) : Prop where
  A₁ : C.A₁.InputsLt n
  σ₁ : C.σ₁.InputsLt n
  A₂ : C.A₂.InputsLt n
  σ₂ : C.σ₂.InputsLt n
  A₃ : C.A₃.InputsLt n
  σ₃ : C.σ₃.InputsLt n

variable (e G : ℕ)

/-! ### Same-variable formulas -/

/-- `cellEq`. -/
def cellEqF (A B : FieldsF) : Fml :=
  andList [eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p, eqFields A.v B.v]

/-- `headEq`. -/
def headEqF (A B : FieldsF) : Fml := andList [eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p]

/-- `stateEq`. -/
def stateEqF (A B : FieldsF) : Fml := andList [eqFields A.t B.t, eqFields A.q B.q]

/-- `auxEq`. -/
def auxEqF (A B : FieldsF) : Fml :=
  andList ([eqFields A.t B.t, eqFields A.g B.g] ++ List.ofFn fun k : Fin 13 => eqFields (A.js k) (B.js k))

/-- `samePos`. -/
def samePosF (A B : FieldsF) : Fml := andList [eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p]

section EqF

variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB

end EqF

section EqInputs

variable {n : ℕ} {A B : FieldsF} (hA : A.InputsLt n) (hB : B.InputsLt n)
include hA hB

end EqInputs

/-! ### Unit clauses and signs -/

/-- `UnitCell`. -/
def unitCellF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, cellEqF C.A₁ C.A₂, cellEqF C.A₁ C.A₃]

/-- `UnitHead`. -/
def unitHeadF (C : CandF) : Fml :=
  andList [isHeadF e C.A₁, isHeadF e C.A₂, isHeadF e C.A₃, headEqF C.A₁ C.A₂, headEqF C.A₁ C.A₃]

/-- `UnitState`. -/
def unitStateF (C : CandF) : Fml :=
  andList [isStateF e C.A₁, isStateF e C.A₂, isStateF e C.A₃, stateEqF C.A₁ C.A₂, stateEqF C.A₁ C.A₃]

/-- `UnitEmitBad`. -/
def unitEmitBadF (C : CandF) : Fml :=
  andList [isEmitBadF e C.A₁, isEmitBadF e C.A₂, isEmitBadF e C.A₃, eqFields C.A₁.t C.A₂.t,
    eqFields C.A₁.t C.A₃.t]

/-- `UnitEmitted`. -/
def unitEmittedF (C : CandF) : Fml :=
  andList [isEmittedF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, eqFields C.A₁.t C.A₂.t,
    eqFields C.A₁.t C.A₃.t]

/-- `UnitAux`. -/
def unitAuxF (C : CandF) : Fml :=
  andList [isAuxF e G C.A₁, isAuxF e G C.A₂, isAuxF e G C.A₃, auxEqF C.A₁ C.A₂, auxEqF C.A₁ C.A₃]

/-- `SameSigns`. -/
def sameSignsF (C : CandF) : Fml := and (xnor C.σ₂ C.σ₁) (xnor C.σ₃ C.σ₁)

section UnitF

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

end UnitF

section UnitInputs

variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC

end UnitInputs

/-! ### Positions and values -/

/-- `Bdry S p`. -/
def bdryF (A : FieldsF) : Fml :=
  or (ltConst A.p (nbits (W e) 2)) (not (ltConst A.p (nbits (W e) (2 * Sof e + 5))))

/-- `p = 3` for an input tape, `S + 3` for a work tape: the start cell. -/
def startCellF (A : FieldsF) : Fml :=
  mux (ltConst A.d (nbits 4 7)) (eqConst A.p (nbits (W e) 3)) (eqConst A.p (nbits (W e) (Sof e + 3)))

/-- `v = workCode S p`. -/
def workValF (A : FieldsF) : Fml :=
  mux (bdryF e A) (eqConst A.v (nbits 3 6)) (eqConst A.v (nbits 3 5))

/-- The lookup table of a string of codes from cell `k`: `p = k + i ∧ v = codes[i]`. -/
def lookupList (A : FieldsF) : ℕ → List ℕ → List Fml
  | _, [] => []
  | k, c :: cs => and (eqConst A.p (nbits (W e) k)) (eqConst A.v (nbits 3 c)) :: lookupList A (k + 1) cs

/-- `v = cellCode x S p` for the string `x` of codes `codes`, of length at most `S`. -/
def cellValF (A : FieldsF) (codes : List ℕ) : Fml :=
  mux (bdryF e A) (eqConst A.v (nbits 3 6))
    (mux (and (not (ltConst A.p (nbits (W e) 3))) (ltConst A.p (nbits (W e) (codes.length + 3))))
      (orList (lookupList e A 3 codes)) (eqConst A.v (nbits 3 5)))

/-- `v = cellCode 1^T S p`. -/
def unaryValF (T : ℕ) (A : FieldsF) : Fml :=
  mux (bdryF e A) (eqConst A.v (nbits 3 6))
    (mux (and (not (ltConst A.p (nbits (W e) 3))) (ltConst A.p (nbits (W e) (T + 3))))
      (eqConst A.v (nbits 3 1)) (eqConst A.v (nbits 3 5)))

/-- The codes of a string. -/
def codesOf (x : List Sym) : List ℕ := x.map fun s => symCode (.sym s)

section ValF

variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA

end ValF

section ValInputs

variable {n : ℕ} {A : FieldsF} (hA : A.InputsLt n)
include hA

end ValInputs

/-! ## More helpers -/

/-- The tapes `fixed j = none` are the indices `frees`. -/
structure FreeSpec (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ) : Prop where
  lt : ∀ j ∈ frees, j < 7
  iff : ∀ j : Fin 7, fixed j = none ↔ (j : ℕ) ∈ frees

/-- The entries `(j, vf)` of `tabs` are the fixed tapes `fixed j = some x`, with `vf` computing
`v = cellCode x S p` on the record `A`. -/
structure TapeSpec (e : ℕ) (A : FieldsF) (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml)) :
    Prop where
  entry : ∀ jv ∈ tabs, ∃ (j : Fin 7) (x : List Sym), jv.1 = j ∧ fixed j = some x ∧
    ∀ x' : ℕ → Bool, jv.2.eval x' = decide ((evalFields A x').v = cellCode x (Sof e) (evalFields A x').p)
  complete : ∀ (j : Fin 7) (x : List Sym), fixed j = some x → ∃ vf, ((j : ℕ), vf) ∈ tabs

variable (e G : ℕ)

/-- `FreeTape`. -/
def freeTapeF (frees : List ℕ) (A : FieldsF) : Fml := orList (frees.map fun j => eqConst A.d (nbits 4 j))

/-- `t = 0`. -/
def tZeroF (A : FieldsF) : Fml := eqConst A.t (nbits (W e) 0)

/-! ## The start family -/

section Start

variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))

/-- `StartHead`. -/
def startHeadF (C : CandF) : Fml :=
  andList [unitHeadF e C, sameSignsF C, tZeroF e C.A₁, xnor C.σ₁ (startCellF e C.A₁)]

/-- `StartState`. -/
noncomputable def startStateF (C : CandF) : Fml :=
  andList [unitStateF e C, sameSignsF C, tZeroF e C.A₁,
    xnor C.σ₁ (eqConst C.A₁.q (nbits Qb (qCode (some U.q₀))))]

/-- `StartFixed`, for the tapes `tabs`. -/
def startFixedF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁,
    orList (tabs.map fun jv => and (eqConst C.A₁.d (nbits 4 jv.1)) (xnor C.σ₁ jv.2))]

/-- `StartWork`. -/
def startWorkF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, not (ltConst C.A₁.d (nbits 4 7)),
    xnor C.σ₁ (workValF e C.A₁)]

/-- `StartPred`. -/
noncomputable def startF (C : CandF) : Fml :=
  orList [startHeadF e C, startStateF e C, startFixedF e tabs C, startWorkF e C]

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

end Start

section StartInputs

variable {n : ℕ} (tabs : List (ℕ × Fml)) (htabs : ∀ jv ∈ tabs, jv.2.InputsLt n) {C : CandF}
  (hC : C.InputsLt n)
include hC

end StartInputs

/-! ## The free family -/

section Free

variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)

/-- `FreeBdry`. -/
def freeBdryF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, freeTapeF frees C.A₁, bdryF e C.A₁,
    xnor C.σ₁ (eqConst C.A₁.v (nbits 3 6))]

/-- `FreeOther`. -/
def freeOtherF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, freeTapeF frees C.A₁, not (bdryF e C.A₁),
    not (eqConst C.A₁.v (nbits 3 0)), not (eqConst C.A₁.v (nbits 3 1)), not (eqConst C.A₁.v (nbits 3 5)),
    not C.σ₁]

/-- `FreeTwo`. -/
def freeTwoF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁, freeTapeF frees C.A₁,
    eqConst C.A₁.p (nbits (W e) 2), xnor C.σ₁ (eqConst C.A₁.v (nbits 3 5))]

/-- `FreeOneOf`. -/
def freeOneOfF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, samePosF C.A₁ C.A₂, samePosF C.A₁ C.A₃,
    tZeroF e C.A₁, freeTapeF frees C.A₁, not (bdryF e C.A₁), eqConst C.A₁.v (nbits 3 0),
    eqConst C.A₂.v (nbits 3 1), eqConst C.A₃.v (nbits 3 5), C.σ₁, C.σ₂, C.σ₃]

/-- `FreeNand`. -/
def freeNandF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, samePosF C.A₁ C.A₂, cellEqF C.A₂ C.A₃,
    tZeroF e C.A₁, freeTapeF frees C.A₁, not (bdryF e C.A₁), not (eqFields C.A₁.v C.A₂.v),
    not C.σ₁, not C.σ₂, not C.σ₃]

/-- `FreeBlank`. -/
def freeBlankF (C : CandF) : Fml :=
  andList [isCellF e C.A₁, isCellF e C.A₂, isCellF e C.A₃, cellEqF C.A₂ C.A₃, tZeroF e C.A₁,
    freeTapeF frees C.A₁, eqFields C.A₂.t C.A₁.t, eqFields C.A₂.d C.A₁.d,
    not (ltConst C.A₁.p (nbits (W e) 3)), not (bdryF e C.A₂), ltFields C.A₁.p C.A₂.p,
    eqConst C.A₁.v (nbits 3 5), eqConst C.A₂.v (nbits 3 5), not C.σ₁, C.σ₂, C.σ₃]

/-- `FreePred`. -/
def freeF (C : CandF) : Fml :=
  orList [freeBdryF e frees C, freeOtherF e frees C, freeTwoF e frees C, freeOneOfF e frees C,
    freeNandF e frees C, freeBlankF e frees C]

variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC

end Free

section FreeInputs

variable {n : ℕ} (frees : List ℕ) {C : CandF} (hC : C.InputsLt n)
include hC

end FreeInputs

/-! ## The boundary, emission and final families -/

/-- `BdryCell`. -/
def bdryCellF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, bdryF e C.A₁, xnor C.σ₁ (eqConst C.A₁.v (nbits 3 6))]

/-- `BdryHead`. -/
def bdryHeadF (C : CandF) : Fml :=
  andList [unitHeadF e C, sameSignsF C, bdryF e C.A₁, not C.σ₁]

/-- `BdryPred`. -/
def bdryPredF (C : CandF) : Fml := or (bdryCellF e C) (bdryHeadF e C)

/-- `EmitZero`. -/
def emitZeroF (C : CandF) : Fml :=
  andList [unitEmittedF e C, sameSignsF C, tZeroF e C.A₁, not C.σ₁]

/-- `EmitStep`. -/
def emitStepF (C : CandF) : Fml :=
  andList [isEmittedF e C.A₁, isEmittedF e C.A₂, isEmitOneF e C.A₃, addConstRel C.A₃.t C.A₁.t (nbits (W e) 1),
    eqFields C.A₂.t C.A₃.t, not C.σ₁, C.σ₂, C.σ₃]

/-- `EmitMono`. -/
def emitMonoF (C : CandF) : Fml :=
  andList [isEmittedF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, ltConst C.A₁.t (nbits (W e) (Sof e)),
    addConstRel C.A₁.t C.A₂.t (nbits (W e) 1), eqFields C.A₃.t C.A₂.t, not C.σ₁, C.σ₂, C.σ₃]

/-- `EmitOne`. -/
def emitOneF (C : CandF) : Fml :=
  andList [isEmitOneF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, addConstRel C.A₁.t C.A₂.t (nbits (W e) 1),
    eqFields C.A₃.t C.A₂.t, not C.σ₁, C.σ₂, C.σ₃]

/-- `EmitOnce`. -/
def emitOnceF (C : CandF) : Fml :=
  andList [isEmitOneF e C.A₁, isEmittedF e C.A₂, isEmittedF e C.A₃, eqFields C.A₂.t C.A₁.t,
    eqFields C.A₃.t C.A₂.t, not C.σ₁, not C.σ₂, not C.σ₃]

/-- `EmitBad`. -/
def emitBadF (C : CandF) : Fml := andList [unitEmitBadF e C, sameSignsF C, not C.σ₁]

/-- `EmitPred`. -/
def emitPredF (C : CandF) : Fml :=
  orList [emitZeroF e C, emitStepF e C, emitMonoF e C, emitOneF e C, emitOnceF e C, emitBadF e C]

/-- `FinalState`. -/
noncomputable def finalStateF (C : CandF) : Fml :=
  andList [unitStateF e C, sameSignsF C, eqConst C.A₁.t (nbits (W e) (Sof e)),
    eqConst C.A₁.q (nbits Qb (qCode none)), C.σ₁]

/-- `FinalEmitted`. -/
def finalEmittedF (C : CandF) : Fml :=
  andList [unitEmittedF e C, sameSignsF C, eqConst C.A₁.t (nbits (W e) (Sof e)), C.σ₁]

/-- `FinalPred`. -/
noncomputable def finalPredF (C : CandF) : Fml := or (finalStateF e C) (finalEmittedF e C)

section BEF

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

end BEF

section BEFInputs

variable {n : ℕ} {C : CandF} (hC : C.InputsLt n)
include hC

end BEFInputs

/-! ## The five explicit families -/

/-- `MainPred`. -/
noncomputable def mainF (tabs : List (ℕ × Fml)) (frees : List ℕ) (C : CandF) : Fml :=
  orList [startF e tabs C, freeF e frees C, bdryPredF e C, emitPredF e C, finalPredF e C]

/-! ## The window family

The templates of the check circuit enter the formula as data: a window variable is a
*descriptor* (`WDesc`: a one-hot kind, and the tape, offset, value and state as bit strings),
a literal spec an `LDesc`, so that the describer program builds the window formula by a fold
over a constant list of descriptors, never inspecting a `WinVar` or a `Gate`. -/

/-- The one-hot vector of length `n` with its `k`-th entry set. -/
def oneHot (n k : ℕ) : List Bool := (List.range n).map fun i => decide (i = k)

@[simp] theorem length_oneHot (n k : ℕ) : (oneHot n k).length = n := by simp [oneHot]

/-- Select by a one-hot vector: `⋁ᵢ bᵢ ∧ fᵢ`. -/
def selectF (hot : List Bool) (fs : List Fml) : Fml :=
  orList (List.zipWith (fun b f => and (const b) f) hot fs)

/-- A window variable as data: the kind (one-hot over `cellPre`, `headPre`, `cellPost`,
`headPost`, `statePre`, `statePost`, `emitOne`, `emitBad`), the tape (4 bits, and one-hot over
the 13 tapes), the offset (3 bits), the value (3 bits), the state (`Qb` bits). -/
structure WDesc where
  kind : List Bool
  d : BitStr
  dHot : List Bool
  δ : BitStr
  v : BitStr
  q : BitStr

/-- The descriptor of a window variable. -/
noncomputable def wvDesc : WinVar 7 6 Sym Ctl → WDesc
  | .cellPre d δ v =>
    ⟨oneHot 8 0, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 δ, nbits 3 (symCode v), nbits Qb 0⟩
  | .headPre d δ => ⟨oneHot 8 1, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 δ, nbits 3 0, nbits Qb 0⟩
  | .cellPost d v =>
    ⟨oneHot 8 2, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 2, nbits 3 (symCode v), nbits Qb 0⟩
  | .headPost d => ⟨oneHot 8 3, nbits 4 (tapeCode d), oneHot 13 (tapeCode d), nbits 3 2, nbits 3 0, nbits Qb 0⟩
  | .statePre q => ⟨oneHot 8 4, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb (qCode q)⟩
  | .statePost q => ⟨oneHot 8 5, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb (qCode q)⟩
  | .emitOne => ⟨oneHot 8 6, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb 0⟩
  | .emitBad => ⟨oneHot 8 7, nbits 4 0, oneHot 13 0, nbits 3 0, nbits 3 0, nbits Qb 0⟩

/-- The descriptor of nothing: no kind. -/
def badDesc : WDesc := ⟨List.replicate 8 false, [], [], [], [], []⟩

/-- `p = js_d + δ`, the tape `d` given one-hot. -/
def posF (Fa A : FieldsF) (dHot : List Bool) (δ : BitStr) : Fml :=
  selectF dHot ((List.ofFn Fa.js).map fun js => addConstRel js A.p (padBits (W e) δ))

/-- `WinMatch`, on a descriptor. -/
def winMatchN (Fa A : FieldsF) (w : WDesc) : Fml :=
  selectF w.kind [
    andList [isCellF e A, eqFields A.t Fa.t, eqConst A.d w.d, posF e Fa A w.dHot w.δ, eqConst A.v w.v],
    andList [isHeadF e A, eqFields A.t Fa.t, eqConst A.d w.d, posF e Fa A w.dHot w.δ],
    andList [isCellF e A, addConstRel Fa.t A.t (nbits (W e) 1), eqConst A.d w.d, posF e Fa A w.dHot w.δ,
      eqConst A.v w.v],
    andList [isHeadF e A, addConstRel Fa.t A.t (nbits (W e) 1), eqConst A.d w.d, posF e Fa A w.dHot w.δ],
    andList [isStateF e A, eqFields A.t Fa.t, eqConst A.q w.q],
    andList [isStateF e A, addConstRel Fa.t A.t (nbits (W e) 1), eqConst A.q w.q],
    andList [isEmitOneF e A, eqFields A.t Fa.t],
    andList [isEmitBadF e A, eqFields A.t Fa.t]]

/-- `SpecMatch` for a gate spec, with the gate index as bits. -/
def auxMatchN (Fa A : FieldsF) (u : BitStr) : Fml :=
  andList ([isAuxF e G A, eqFields A.t Fa.t, eqConst A.g u] ++
    List.ofFn fun k : Fin 13 => eqFields (A.js k) (Fa.js k))

/-- A literal spec as data. -/
structure LDesc where
  isAux : Bool
  u : BitStr
  w : WDesc

/-- `SpecMatch`, on a descriptor. -/
def specMatchN (Fa A : FieldsF) (l : LDesc) : Fml :=
  mux (const l.isAux) (auxMatchN e G Fa A l.u) (winMatchN e Fa A l.w)

/-- The descriptors of the window variables, in the canonical order. -/
noncomputable def wvDescs : List WDesc :=
  (List.finRange (winCard 7 6 Sym Ctl)).map fun i => wvDesc ((Fintype.equivFin _).symm i)

/-- The descriptor of a spec. -/
noncomputable def LitSpec.toN : LitSpec → LDesc
  | .aux u => ⟨true, nbits (Gb G) u, badDesc⟩
  | .win n => ⟨false, [], wvDescs.getD n badDesc⟩

/-- A template as data. -/
abbrev NTpl := (LDesc × Bool) × (LDesc × Bool) × (LDesc × Bool)

/-- The descriptor of a template. -/
noncomputable def Tpl.toN (tp : Tpl) : NTpl :=
  ((LitSpec.toN G tp.1.1, tp.1.2), (LitSpec.toN G tp.2.1.1, tp.2.1.2), (LitSpec.toN G tp.2.2.1, tp.2.2.2))

/-- `TplMatch`, on a descriptor. -/
def tplN (tp : NTpl) (C : CandF) : Fml :=
  andList [specMatchN e G C.A₃ C.A₁ tp.1.1, xnor C.σ₁ (const tp.1.2), specMatchN e G C.A₃ C.A₂ tp.2.1.1,
    xnor C.σ₂ (const tp.2.1.2), specMatchN e G C.A₃ C.A₃ tp.2.2.1, xnor C.σ₃ (const tp.2.2.2)]

/-- The template descriptors of the gates `gs`, numbered from `g₀`. -/
noncomputable def tplsFrom : ℕ → List Gate → List (List NTpl)
  | _, [] => []
  | g, gate :: gs => (gateTemplates g gate).map (Tpl.toN G) :: tplsFrom (g + 1) gs

/-- The template descriptors of the check circuit: the constant of the describer. -/
noncomputable def tplsOf (chk : Circuit) : List (List NTpl) := tplsFrom G 0 chk.gates

/-- `WindowGates`, on the descriptors `tpls`. -/
def windowGatesN (tpls : List (List NTpl)) (C : CandF) : Fml :=
  orList (tpls.map fun l => orList (l.map fun tp => tplN e G tp C))

/-- `WindowOut`. -/
def windowOutF (C : CandF) : Fml :=
  andList [unitAuxF e G C, sameSignsF C, eqConst C.A₁.g (nbits (Gb G) (G - 1)), C.σ₁]

/-- `WindowPred`. -/
def windowN (tpls : List (List NTpl)) (C : CandF) : Fml := or (windowGatesN e G tpls C) (windowOutF e G C)

section WindowEval

variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA

end WindowEval

section WindowEval'

variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC

end WindowEval'

section WindowInputs

variable {n : ℕ}

end WindowInputs

/-! ## The whole tableau -/

/-- The formula of the tableau on a candidate: the five explicit families or the window family. -/
noncomputable def tableauF (tabs : List (ℕ × Fml)) (frees : List ℕ) (tpls : List (List NTpl)) (C : CandF) : Fml :=
  or (mainF e tabs frees C) (windowN e G tpls C)

end MIPRE.TM.CookLevin.Desc


