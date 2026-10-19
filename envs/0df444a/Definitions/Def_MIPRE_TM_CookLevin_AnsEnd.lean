-- Prove2me | Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
-- name    : MIPRE_TM_CookLevin_AnsEnd
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:09:18.008673+00:00
-- url     : https://prove2.me/theorems/e553f9e3-de7d-436b-a852-7324a93e28a1
-- title:
--   Definitions of AnsEnd: The answer tapes end at `T` Two clauses beyond the tableau: the cell at position `T + 3` of each of the two free tapes…
-- statement:
--   The definitions of the module `MIPRE.TM.CookLevin.AnsEnd` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answer tapes end at `T`. Two clauses beyond the tableau: the cell at position `T + 3` of each of the two free tapes holds the blank. They are what makes the soundness direction of the describer give answers of length at most `T`: the free-tape clauses force the blanks of a free tape to be trailing (`freeClauses`), so a blank at `T + 3` bounds the string read off the time-`0` row by `T` (`freeLen`, `Sound.lean`). An accepting run on answers of length at most `T` satisfies them, so they cost the completeness direction nothing. `tableauPlus` is the tableau together with them, `tableauPlusF`…
--
--   **Definitions** (5): `MIPRE.TM.CookLevin.Desc.AnsEnd` (The candidate is one of the two answer-end clauses.); `MIPRE.TM.CookLevin.Desc.ansEndClauses` (The two clauses: the cell at position `T + 3` of a free tape holds the blank.); `MIPRE.TM.CookLevin.Desc.ansEndF` (`AnsEnd`.); `MIPRE.TM.CookLevin.Desc.tableauPlus` (The tableau together with the two answer-end clauses: the clause set the describer describes.); `MIPRE.TM.CookLevin.Desc.tableauPlusF` (The formula of the whole clause set.).
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.CookLevin.AnsEnd` (`MIPRE/TM/CookLevin/AnsEnd.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 51 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/AnsEnd.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/AnsEnd.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
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
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params

/-!
# The answer tapes end at `T`

Two clauses beyond the tableau: the cell at position `T + 3` of each of the two free tapes
holds the blank. They are what makes the soundness direction of the describer give answers of
length at most `T`: the free-tape clauses force the blanks of a free tape to be trailing
(`freeClauses`), so a blank at `T + 3` bounds the string read off the time-`0` row by `T`
(`freeLen`, `Sound.lean`). An accepting run on answers of length at most `T` satisfies them,
so they cost the completeness direction nothing.

`tableauPlus` is the tableau together with them, `tableauPlusF` the formula, and
`eval_tableauPlusF` its exactness (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

variable (e G T : ℕ)

/-- The two clauses: the cell at position `T + 3` of a free tape holds the blank. -/
def ansEndClauses : Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G) :=
  {c | ∃ (j : Fin 7) (p : Pos (Sof e)), ((j : ℕ) = 5 ∨ (j : ℕ) = 6) ∧ (p : ℕ) = T + 3 ∧
    c = unit (.cell 0 (.inl j) p .blank) true}

/-- The candidate is one of the two answer-end clauses. -/
def AnsEnd (c : Cand) : Prop :=
  UnitCell e c ∧ SameSigns c ∧ c.F₁.t = 0 ∧ (c.F₁.d = 5 ∨ c.F₁.d = 6) ∧ c.F₁.p = T + 3 ∧
    c.F₁.v = 5 ∧ c.s₁ = true

/-- The tableau together with the two answer-end clauses: the clause set the describer
describes. -/
noncomputable def tableauPlus (fixed : Fin 7 → Option (List Sym)) (chk : Circuit) :
    Cnf3 (TabVar 7 6 Sym Ctl (Sof e) chk.gates.length) :=
  tableau U Sym.zero Sym.one (Sof e) fixed chk ∪ ansEndClauses e chk.gates.length T

/-! ## As a formula -/

/-- `AnsEnd`. -/
def ansEndF (C : CandF) : Fml :=
  andList [unitCellF e C, sameSignsF C, tZeroF e C.A₁,
    or (eqConst C.A₁.d (nbits 4 5)) (eqConst C.A₁.d (nbits 4 6)),
    eqConst C.A₁.p (nbits (W e) (T + 3)), eqConst C.A₁.v (nbits 3 5), C.σ₁]

/-- The formula of the whole clause set. -/
noncomputable def tableauPlusF (tabs : List (ℕ × Fml)) (frees : List ℕ) (tpls : List (List NTpl))
    (C : CandF) : Fml :=
  or (tableauF e G tabs frees tpls C) (ansEndF e T C)

end MIPRE.TM.CookLevin.Desc


