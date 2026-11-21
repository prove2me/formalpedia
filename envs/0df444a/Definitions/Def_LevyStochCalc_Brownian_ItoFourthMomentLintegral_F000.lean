-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
-- name    : LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:06:09.635179+00:00
-- url     : https://prove2.me/theorems/ae569dd3-ce93-4e41-bcf1-f42fca155d46
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentLintegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentLintegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Fourth moment of the `L²` Itô integral

Truncation of a simple integrand and the `lintegral` form of the fourth-moment bound. Clamping
the coefficients to `[-C, C]` (`SimplePredictable.truncate`) moves a value no further from a
target already in `[-C, C]`, so a truncated approximant is still an approximant; the bound for
the simple integrands then passes to the `L²` Itô integral of any integrand bounded by `C` by
Fatou along an almost-everywhere convergent subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A function fixing `0` commutes with a step sum over a strictly monotone partition. -/
theorem comp_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f : Fin M → ℝ) (s : ℝ) (g : ℝ → ℝ) (hg0 : g 0 = 0) :
    g (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g (f j) else 0 := by
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
    rw [hsum f, hsum fun j => g (f j)]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz f, hz fun j => g (f j), hg0]
/-- The coefficients of a simple integrand clamped to `[-C, C]`. -/
noncomputable def SimplePredictable.truncate {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ) :
    SimplePredictable Ω T where
  N := G.N
  partition := G.partition
  partition_zero := G.partition_zero
  partition_le_T := G.partition_le_T
  partition_strictMono := G.partition_strictMono
  ξ := fun i ω => max (-C) (min C (G.ξ i ω))
  ξ_bounded := fun i => ⟨|C|, fun ω => abs_le.mpr
    ⟨le_max_of_le_left (neg_le_neg (le_abs_self C)),
      max_le (neg_le_abs C) ((min_le_left C (G.ξ i ω)).trans (le_abs_self C))⟩⟩
  ξ_measurable := fun i =>
    measurable_const.max (measurable_const.min (G.ξ_measurable i))
theorem SimplePredictable.abs_truncate_xi_le {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (i : Fin G.N) (ω : Ω) : |(G.truncate C).ξ i ω| ≤ C := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
theorem SimplePredictable.truncate_eval {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (s : ℝ) (ω : Ω) :
    (G.truncate C).eval s ω = max (-C) (min C (G.eval s ω)) := by
  have hg0 : max (-C) (min C (0 : ℝ)) = 0 := by
    rw [min_eq_right hC, max_eq_right (by linarith : -C ≤ (0 : ℝ))]
  exact (comp_sum_ite G.partition_strictMono (fun i => G.ξ i ω) s
    (fun x => max (-C) (min C x)) hg0).symm
theorem SimplePredictable.truncate_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    ∀ i : Fin (G.truncate C).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((G.truncate C).partition i.castSucc)) ((G.truncate C).ξ i) := by
  intro i
  exact (measurable_const.max
    (measurable_const.min (h_adapt i).measurable)).stronglyMeasurable
section LintegralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end LintegralForm

end LevyStochCalc.Brownian.Ito


