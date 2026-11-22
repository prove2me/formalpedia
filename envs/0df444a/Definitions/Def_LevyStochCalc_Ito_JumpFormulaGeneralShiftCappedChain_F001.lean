-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001
-- name    : LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:46:58.797472+00:00
-- url     : https://prove2.me/theorems/fa994174-4706-48b3-8185-a94ccf3cee18
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F000
import Definitions.Def_SourceProof_4574c5c52c160c5cb88ceea7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The capped jump chain over a prescribed evaluation path

The pathwise sum of the jumps carried by a mark set over a window reads the jump coefficient at a
prescribed path of states, and capping the arrival times at the horizon turns that sum into the
chain of jumps accumulated up to each arrival time. Over an enumeration of the atoms of the
window the jump sum is the sum of the jump coefficient over the enumerated atoms whose times lie
in the sub-window, so the capped sum gains exactly the jump coefficient carried by each arrival
time inside the window and does not move strictly between consecutive arrival times; a path that
splits at all nonnegative times into a continuous part and that jump sum is therefore the
continuous part translated by the capped jump sum on each such interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Defs

end Defs

section GeneralShift

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (A : Set E)

end GeneralShift

section MarkIdentification

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- The jump sum over the whole enumerated window is the sum of the jump coefficient over the
enumerated atoms. -/
theorem jumpSumAt_eq_sum_atomEnum_horizon (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) :
    jumpSumAt X Y A T ω = ∑ j : Fin K, coeffs.γ (θ j) (Y (θ j) ω) (ε j) := by
  classical
  funext i
  rw [Finset.sum_apply, _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 X Y hA hmem hsum le_rfl i]
  exact Finset.sum_congr rfl fun j _ => if_pos (hmem j).1.2
end MarkIdentification

section CappedChain

variable {A : Set E}

end CappedChain

end LevyStochCalc.Ito.JumpFormula


