-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_DeciderCost
-- name    : MIPRE_Foundations_Repeat_DeciderCost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T15:43:23.186777+00:00
-- url     : https://prove2.me/theorems/bbb8c9bc-7981-4e66-9d4f-23d60453794e
-- title:
--   Definitions of DeciderCost: The running time of the repeated decider `repDecider_timeBound`: when the input sampler and decider run within `R.S…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.DeciderCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The running time of the repeated decider. `repDecider_timeBound`: when the input sampler and decider run within `R.S (|d| + 1)^{R.k}` and `R.D (|d| + 1)^{R.k}` at index `n`, the repeated decider on `(λ, τ, β)` runs within `c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything and `W` any number dominating the parameters (`DecDom`). The cost is the explicit one of `prepProg_runs` and `coordLoop_runs_bounded`, dominated piece by piece as in `SamplerCost.lean`; the one point of care is that the sanitized inputs of the loop are no larger than the raw ones…
--
--   **Definitions** (1): `MIPRE.Repeat.DecDom` (The hypotheses on the dominating number `W`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.DeciderCost` (`MIPRE/Foundations/Repeat/DeciderCost.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 44 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/DeciderCost.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DeciderCost.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Theorems.Thm_MIPRE_Cost_hardcode_time

/-!
# The running time of the repeated decider

`repDecider_timeBound`: when the input sampler and decider run within `R.S (|d| + 1)^{R.k}`
and `R.D (|d| + 1)^{R.k}` at index `n`, the repeated decider on `(λ, τ, β)` runs within
`c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything and
`W` any number dominating the parameters (`DecDom`). The cost is the explicit one of
`prepProg_runs` and `coordLoop_runs_bounded`, dominated piece by piece as in
`SamplerCost.lean`; the one point of care is that the sanitized inputs of the loop are no larger
than the raw ones (`size_encode_bitsOf_le`, `size_parse_bitsOf_le`), so that the input decider
is called on data of size below `|d|` and its bound needs no factor `c^{R.k}`.
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-! ## Sizes of the sanitized inputs -/

/-! ## Domination of the primitives' costs -/

section Chain

variable {W X K : ℕ}

end Chain

/-! ## The calls of the loop -/

/-! ## The running time -/

/-- The hypotheses on the dominating number `W`. -/
structure DecDom {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider) (lam tau beta n : ℕ) (R : Budget)
    (W : ℕ) : Prop where
  S_le : R.S ≤ W
  D_le : R.D ≤ W
  lam_le : lam ≤ W
  tau_le : tau ≤ W
  beta_le : beta ≤ W
  n_le : n ≤ W
  sizeS_le : esize S.prog ≤ W
  sizeD_le : esize D.prog ≤ W
  pow_le : 10 ^ R.k ≤ W
  reps_le : Repetition.reps lam tau n ≤ W
  parse_le : Repetition.parseBound lam beta n ≤ W
  dim_le : S.dim n ≤ W

end MIPRE.Repeat


