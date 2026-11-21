-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
-- name    : LevyStochCalc_Brownian_ItoAlgebraProduct_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:39:12.374128+00:00
-- url     : https://prove2.me/theorems/4d84e840-bb44-4c92-9fa3-5c9d3eae2f13
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoAlgebraProduct
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoAlgebraProduct. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Products of simple integrands and elementary integrals against a process

Two simple integrands with a common final partition point multiply to a simple integrand carried
on their common refinement, whose evaluation is the pointwise product of the evaluations and
whose adaptedness is inherited; summing the increments of the elementary integral of one against
the coefficients of the other is the elementary integral of that product, and the difference
between an elementary integral and an `L²` Itô integral obeys the Itô isometry.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- At most one cell of a strictly monotone partition contains a given time, so a product of
two step sums over that partition is the step sum of the pointwise product. -/
theorem sum_ite_mul_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f g : Fin M → ℝ) (s : ℝ) :
    (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      * (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j * g j else 0 := by
  classical
  by_cases h : ∃ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ → j = j₀ := by
      intro j hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (j.succ : Fin (M + 1)) ≤ j₀.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
        exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hj₀.1)
      · have hle : (j₀.succ : Fin (M + 1)) ≤ j.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
        exact absurd (hj₀.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
    have hsum : ∀ h : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h j else 0) = h j₀ := by
      intro h
      rw [Finset.sum_eq_single j₀ (fun j _ hjne => if_neg fun hc => hjne (huniq j hc))
        (fun hnm => absurd (Finset.mem_univ _) hnm)]
      exact if_pos hj₀
    rw [hsum f, hsum g, hsum fun j => f j * g j]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz f, hz g, hz fun j => f j * g j, mul_zero]
/-- The product of two simple integrands, carried on their common refinement. -/
noncomputable def SimplePredictable.mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := (_root_.Prove2MeSourceProof.h_3281419cf2ade5797eb4da52 H₁) H₂
  partition_le_T := ((_root_.Prove2MeSourceProof.h_04cf3c59e383c3e0f39e729b H₁) H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    refine ⟨max C₁ 0 * max C₂ 0, fun ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hC₁ ω).trans (le_max_left _ _)) ((hC₂ ω).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).mul (H₂.ξ_measurable _)
section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end SimpleVsGeneral

end LevyStochCalc.Brownian.Ito


