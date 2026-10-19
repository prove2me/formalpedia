-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_Kinds
-- name    : MIPRE_TM_CookLevin_Kinds
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:59.00199+00:00
-- url     : https://prove2.me/theorems/8bc75dbb-3356-40cf-a7ce-68063f8ea2cd
-- title:
--   Definitions of Kinds: The kinds of variables, on fields and as formulas For the fields `F` of an index, the predicates `IsCell`, `IsHead`, ……
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.Kinds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The kinds of variables, on fields and as formulas. For the fields `F` of an index, the predicates `IsCell`, `IsHead`, … saying that `F` denotes a variable of that kind (with its range checks), the characterization of `decodeVar` by them (`decodeVar_cell_iff`, …), the numeric equality of two fields records (`Fields.numEq`, the same variable up to the aliasing of unused fields), and the formulas computing all of these on the field formulas of a literal (`isCellF`, `numEqF`, …) with their semantics (`planning/succinct-cook-levin.md`, S3).
--
--   **Definitions** (16): `MIPRE.TM.CookLevin.Desc.FieldsF.Lengths` (The lengths of the field formulas of a literal.); `MIPRE.TM.CookLevin.Desc.IsAux` (The fields denote a gate variable.); `MIPRE.TM.CookLevin.Desc.IsCell` (The fields denote a cell variable.); `MIPRE.TM.CookLevin.Desc.IsEmitBad` (The fields denote an `emitBad` variable.); `MIPRE.TM.CookLevin.Desc.IsEmitOne` (The fields denote an `emitOne` variable.); `MIPRE.TM.CookLevin.Desc.IsEmitted` (The fields denote an `emitted` variable.); `MIPRE.TM.CookLevin.Desc.IsHead` (The fields denote a head variable.); `MIPRE.TM.CookLevin.Desc.IsState` (The fields denote a state variable.); `MIPRE.TM.CookLevin.Desc.isAuxF` (The formula: `A` denotes a gate variable.); `MIPRE.TM.CookLevin.Desc.isCellF` (The formula: `A` denotes a cell variable.); `MIPRE.TM.CookLevin.Desc.isEmitBadF` (The formula: `A` denotes an `emitBad` variable.); `MIPRE.TM.CookLevin.Desc.isEmitOneF` (The formula: `A` denotes an `emitOne` variable.); `MIPRE.TM.CookLevin.Desc.isEmittedF` (The formula: `A` denotes an `emitted` variable.); `MIPRE.TM.CookLevin.Desc.isHeadF` (The formula: `A` denotes a head variable.); `MIPRE.TM.CookLevin.Desc.isStateF` (The formula: `A` denotes a state variable.); `MIPRE.TM.CookLevin.Desc.numEqF` (The formula: the numeric fields of `A` and `B` agree.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.Kinds` (`MIPRE/TM/CookLevin/Kinds.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 23 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Kinds.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Kinds.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# The kinds of variables, on fields and as formulas

For the fields `F` of an index, the predicates `IsCell`, `IsHead`, … saying that `F` denotes a
variable of that kind (with its range checks), the characterization of `decodeVar` by them
(`decodeVar_cell_iff`, …), the numeric equality of two fields records (`Fields.numEq`, the
same variable up to the aliasing of unused fields), and the formulas computing all of these
on the field formulas of a literal (`isCellF`, `numEqF`, …) with their semantics
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open SAT Cost Fml

/-! ## Numeric equality of fields -/

/-- The lengths of the field formulas of a literal. -/
structure FieldsF.Lengths (e G : ℕ) (A : FieldsF) : Prop where
  tag : A.tag.length = 3
  t : A.t.length = W e
  d : A.d.length = 4
  p : A.p.length = W e
  v : A.v.length = 3
  q : A.q.length = Qb
  js : ∀ k, (A.js k).length = W e
  g : A.g.length = Gb G

/-- The formula: the numeric fields of `A` and `B` agree. -/
def numEqF (A B : FieldsF) : Fml :=
  andList ([eqFields A.tag B.tag, eqFields A.t B.t, eqFields A.d B.d, eqFields A.p B.p,
    eqFields A.v B.v, eqFields A.q B.q, eqFields A.g B.g] ++
    List.ofFn fun k : Fin 13 => eqFields (A.js k) (B.js k))

/-! ## Kinds -/

section Kinds

/-- The fields denote a cell variable. -/
def IsCell (e : ℕ) (F : Fields) : Prop :=
  (F.flag = true ∧ F.tag = 0 ∧ F.t ≤ Sof e ∧ F.d < 13 ∧ F.p < numCells (Sof e) ∧ F.v < 7) ∨
  (F.flag = false ∧ F.ansOk = true ∧ F.tag = 0 ∧ F.t = 0 ∧ F.d < 7 ∧ F.p < numCells (Sof e) ∧ F.v < 7)

/-- The fields denote a head variable. -/
def IsHead (e : ℕ) (F : Fields) : Prop :=
  F.flag = true ∧ F.tag = 1 ∧ F.t ≤ Sof e ∧ F.d < 13 ∧ F.p < numCells (Sof e)

/-- The fields denote a state variable. -/
def IsState (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 2 ∧ F.t ≤ Sof e ∧ F.q < QC

/-- The fields denote an `emitOne` variable. -/
def IsEmitOne (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 3 ∧ F.t < Sof e

/-- The fields denote an `emitBad` variable. -/
def IsEmitBad (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 4 ∧ F.t < Sof e

/-- The fields denote an `emitted` variable. -/
def IsEmitted (e : ℕ) (F : Fields) : Prop := F.flag = true ∧ F.tag = 5 ∧ F.t ≤ Sof e

/-- The fields denote a gate variable. -/
def IsAux (e G : ℕ) (F : Fields) : Prop :=
  F.flag = true ∧ F.tag = 6 ∧ F.t < Sof e ∧ (∀ k, F.js k < 2 * Sof e + 3) ∧ F.g < G

/-! ### Decoding by kind -/

variable (e G : ℕ)

/-! ### Kinds as formulas -/

/-- The formula: `A` denotes a cell variable. -/
def isCellF (A : FieldsF) : Fml :=
  or (andList [A.flag, eqConst A.tag (nbits 3 0), ltConst A.t (nbits (W e) (Sof e + 1)),
      ltConst A.d (nbits 4 13), ltConst A.p (nbits (W e) (numCells (Sof e))), ltConst A.v (nbits 3 7)])
    (andList [not A.flag, A.ansOk, eqConst A.tag (nbits 3 0), eqConst A.t (nbits (W e) 0),
      ltConst A.d (nbits 4 7), ltConst A.p (nbits (W e) (numCells (Sof e))), ltConst A.v (nbits 3 7)])

/-- The formula: `A` denotes a head variable. -/
def isHeadF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 1), ltConst A.t (nbits (W e) (Sof e + 1)),
    ltConst A.d (nbits 4 13), ltConst A.p (nbits (W e) (numCells (Sof e)))]

/-- The formula: `A` denotes a state variable. -/
def isStateF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 2), ltConst A.t (nbits (W e) (Sof e + 1)),
    ltConst A.q (nbits Qb QC)]

/-- The formula: `A` denotes an `emitOne` variable. -/
def isEmitOneF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 3), ltConst A.t (nbits (W e) (Sof e))]

/-- The formula: `A` denotes an `emitBad` variable. -/
def isEmitBadF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 4), ltConst A.t (nbits (W e) (Sof e))]

/-- The formula: `A` denotes an `emitted` variable. -/
def isEmittedF (A : FieldsF) : Fml :=
  andList [A.flag, eqConst A.tag (nbits 3 5), ltConst A.t (nbits (W e) (Sof e + 1))]

/-- The formula: `A` denotes a gate variable. -/
def isAuxF (A : FieldsF) : Fml :=
  andList ([A.flag, eqConst A.tag (nbits 3 6), ltConst A.t (nbits (W e) (Sof e)),
    ltConst A.g (nbits (Gb G) G)] ++
    List.ofFn fun k : Fin 13 => ltConst (A.js k) (nbits (W e) (2 * Sof e + 3)))

section KindFormulas

variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA

end KindFormulas

end Kinds

end MIPRE.TM.CookLevin.Desc


