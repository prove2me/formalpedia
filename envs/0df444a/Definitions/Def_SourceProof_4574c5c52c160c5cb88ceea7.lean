-- Prove2me | Definitions.Def_SourceProof_4574c5c52c160c5cb88ceea7
-- name    : SourceProof_4574c5c52c160c5cb88ceea7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:41:41.478193+00:00
-- url     : https://prove2.me/theorems/a3d4a1b2-bb46-4183-845a-fdafc6789838
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.JumpFormula.jumpSumAt_eq_sum_atomEnum
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F000

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


theorem _root_.Prove2MeSourceProof.h_4574c5c52c160c5cb88ceea7 (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (i : Fin n) :
    jumpSumAt X Y A t ω i
      = ∑ j : Fin K, if θ j ≤ t then coeffs.γ (θ j) (Y (θ j) ω) (ε j) i else 0 := by
  classical
  have hmt : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ (Set.Ioc (0 : ℝ) t ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
  have hind := hsum ((Set.Ioc (0 : ℝ) t ×ˢ A).indicator
    fun q : ℝ × E => coeffs.γ q.1 (Y q.1 ω) q.2 i)
  rw [setIntegral_indicator hmt, hsub] at hind
  simp only [LevyStochCalc.Ito.JumpFormula.jumpSumAt]
  rw [hind]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : θ j ≤ t
  · have hmemj : ((θ j, ε j) : ℝ × E) ∈ Set.Ioc (0 : ℝ) t ×ˢ A :=
      Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨(hmem j).1.1, hj⟩, (hmem j).2⟩
    rw [if_pos hj, Set.indicator_of_mem hmemj]
  · have hnot : ((θ j, ε j) : ℝ × E) ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hc =>
      hj (Set.mem_Ioc.mp (Set.mem_prod.mp hc).1).2
    rw [if_neg hj, Set.indicator_of_notMem hnot]
end MarkIdentification

section CappedChain

variable {A : Set E}

end CappedChain

end LevyStochCalc.Ito.JumpFormula


