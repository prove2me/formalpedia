-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
-- name    : MIPRE_Foundations_Repeat_SamplerCost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T15:41:07.441769+00:00
-- url     : https://prove2.me/theorems/8e4235cb-2570-4174-b0e4-26aa6734bdbd
-- title:
--   Definitions of SamplerCost: The running time of the repeated sampler `repSampler_timeBound`: when the input sampler runs within `R.S (|d| +…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.SamplerCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The running time of the repeated sampler. `repSampler_timeBound`: when the input sampler runs within `R.S (|d| + 1)^{R.k}` at index `n` and has dimension at most `R.d` there, the repeated sampler on `(λ, τ)` runs within `c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything, `W` any number dominating `R.S`, `R.d`, `λ`, `τ`, `n`, the description length of the input sampler, the repetition count and `10^{R.k}` (the input's time on the dimension query). The cost is the explicit one of `repSampCore_runs_any`, each of whose pieces is a sum and product of quantities…
--
--   **Definitions** (3): `MIPRE.Repeat.SampDom` (The hypotheses on the dominating number `W`.); `MIPRE.Repeat.cU` (The constants of the self-interpreter's overhead polynomial.); `MIPRE.Repeat.dU` (The degree of the self-interpreter's overhead polynomial.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.SamplerCost` (`MIPRE/Foundations/Repeat/SamplerCost.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 38 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/SamplerCost.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/SamplerCost.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic

/-!
# The running time of the repeated sampler

`repSampler_timeBound`: when the input sampler runs within `R.S (|d| + 1)^{R.k}` at index `n`
and has dimension at most `R.d` there, the repeated sampler on `(λ, τ)` runs within
`c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything, `W`
any number dominating `R.S`, `R.d`, `λ`, `τ`, `n`, the description length of the input
sampler, the repetition count and `10^{R.k}` (the input's time on the dimension query). The
cost is the explicit one of `repSampCore_runs_any`, each of whose pieces is a sum and product
of quantities below `W`, below `|d| + 1`, or of the cost of a call to the input sampler
through the universal machine, bounded by `Dom` combinators.
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-- The constants of the self-interpreter's overhead polynomial. -/
noncomputable def cU : ℕ :=
  ∑ i ∈ Finset.range (selfUniversal.bound.natDegree + 1), selfUniversal.bound.coeff i

/-- The degree of the self-interpreter's overhead polynomial. -/
noncomputable def dU : ℕ := selfUniversal.bound.natDegree

/-- The hypotheses on the dominating number `W`. -/
structure SampDom {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ) : Prop where
  S_le : R.S ≤ W
  d_le : R.d ≤ W
  lam_le : lam ≤ W
  tau_le : tau ≤ W
  n_le : n ≤ W
  size_le : esize S.prog ≤ W
  pow_le : 10 ^ R.k ≤ W
  reps_le : Repetition.reps lam tau n ≤ W
  dim_le : S.dim n ≤ W

variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)

/-! ## The domination chain

Each lemma below produces constants `c, m, e` that are uniform in everything, as the
existential outside the universal quantifiers records; the proofs are the `Dom` combinators
applied in the shape of the cost expression, and Lean assembles the constants. -/

section Chain

variable {W X K : ℕ}

/-! The constants of each lemma are natural metavariables assigned by the final `exact`, so
they must be closed terms; `exact ⟨_, _, _, fun … => by …⟩` rather than `refine ⟨?c, …⟩`, whose
synthetic goals the unifier will not assign and instead reduces `max` chains against. -/

end Chain

end MIPRE.Repeat


