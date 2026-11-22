-- Prove2me | Definitions.Def_SourceProof_1ccbf94d189a78e3d3f14cc3
-- name    : SourceProof_1ccbf94d189a78e3d3f14cc3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:02:58.95681+00:00
-- url     : https://prove2.me/theorems/ca4f6575-eac8-46aa-9217-54d0b52a1cb5
-- title:
--   LevyStochCalc source module: SourceProof_1ccbf94d189a78e3d3f14cc3
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.jumpSum_eq_sum_atomEnum` comes from the `LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityDrift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a finite-activity jump path by its arrival times

The jumps of a mark set accumulated up to the arrival times capped at the horizon no longer move
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms, and the in-window members of such a chain are matched one for one with the
entries of the strictly monotone enumeration of the window's atom times. On a mark set of finite
intensity almost every path has an arrival time beyond the horizon, so an identity holding almost
everywhere on each event where the chain has passed the horizon holds almost everywhere. Between
consecutive arrival times inside the window the accumulated jumps gain exactly the jump
coefficient carried by the later arrival time and the mark enumerated with it, and the progressive
measurability of the chain data and of the integrands passes to the right-continuous
regularisation of a filtration.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

end CappedShift

section Reindex

end Reindex

section RightContinuous

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end RightContinuous

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

end Exhaustion

section MarkIdentification

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}


theorem _root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (i : Fin n) :
    LevyStochCalc.Ito.JumpSplitting.jumpSum X A t ω i
      = ∑ j : Fin K, if θ j ≤ t then coeffs.γ (θ j) (X.X (θ j) ω) (ε j) i else 0 := by
  classical
  have hmt : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ (Set.Ioc (0 : ℝ) t ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
  have hind := hsum ((Set.Ioc (0 : ℝ) t ×ˢ A).indicator
    fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
  rw [setIntegral_indicator hmt, hsub] at hind
  simp only [LevyStochCalc.Ito.JumpSplitting.jumpSum]
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

end LevyStochCalc.Ito.JumpFormula


