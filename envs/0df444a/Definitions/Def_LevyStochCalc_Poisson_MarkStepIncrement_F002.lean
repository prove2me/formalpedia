-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F002
-- name    : LevyStochCalc_Poisson_MarkStepIncrement_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:32:28.558235+00:00
-- url     : https://prove2.me/theorems/6f04d572-b8f2-4d51-ba51-d5a220f19f41
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

lemma Adapted.dyadicRestrict {ℓ d : ℕ}
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)} (hG : G.Adapted ℱ) {T' : ℝ} (hT' : 0 < T')
    (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) : (G.dyadicRestrict hT' hd h).Adapted ℱ := by
  intro i hi k
  change @StronglyMeasurable Ω ℝ _ (ℱ ((TimeGrid.dyadic T' hT' (ℓ - d)).p i)) (G.ξ i k)
  rw [dyadic_p_restrict (hT := hT) hT' hd h]
  exact hG i (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))) k
end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The increment of a mark-step integrand over `(s, t]`, weighted by `w`, as a mark-step
integrand on the increment grid. -/
noncomputable def incr (G : MarkStep Ω E ν g) (w : Ω → ℝ) (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C)
    (hwm : Measurable w) (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    MarkStep Ω E ν (g.incr s t hs hst) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => if i = 0 then 0 else w ω * G.ξ (g.startIndex s + (i - 1)) k ω
  ξ_bounded := fun i k => by
    obtain ⟨C, hC⟩ := hw
    obtain ⟨M, hM⟩ := G.ξ_bounded (g.startIndex s + (i - 1)) k
    refine ⟨|C| * |M|, fun ω => ?_⟩
    split_ifs
    · rw [abs_zero]
      positivity
    · rw [abs_mul]
      exact mul_le_mul ((hC ω).trans (le_abs_self C)) ((hM ω).trans (le_abs_self M))
        (abs_nonneg _) (abs_nonneg _)
  ξ_measurable := fun i k => by
    by_cases h : i = 0
    · simp only [h, if_true]
      exact measurable_const
    · simp only [h, if_false]
      exact hwm.mul (G.ξ_measurable _ k)
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

include hw hwm in
lemma Adapted.incr {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w) :
    (G.incr w hw hwm s t hs hst).Adapted ℱ := by
  intro i hi k
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    change @StronglyMeasurable Ω ℝ _ (ℱ ((g.incr s t hs hst).p 0))
      (fun ω => if (0 : ℕ) = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (0 - 1)) k ω)
    simp only [if_true]
    exact stronglyMeasurable_const
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hi' : j + 1 < g.clampIndex t - g.startIndex s + 1 := hi
    have hj : g.startIndex s + j < g.clampIndex t := by omega
    have hlt := g.lt_of_lt_clampIndex hj
    change @StronglyMeasurable Ω ℝ _ (ℱ ((g.incr s t hs hst).p (j + 1)))
      (fun ω => if j + 1 = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (j + 1 - 1)) k ω)
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [g.incr_p_succ]
    have hξ := hG (g.startIndex s + j) hlt.1 k
    rcases Nat.eq_zero_or_pos j with hz | hz
    · subst hz
      rw [add_zero, max_eq_right (g.p_startIndex_le hs.le), min_eq_left hst.le]
      rw [add_zero] at hξ
      exact hwa.mul (hξ.mono (ℱ.mono (g.p_startIndex_le hs.le)))
    · have haN : g.startIndex s < g.N₀ := lt_of_le_of_lt (Nat.le_add_right _ _) hlt.1
      have hgt : s < g.p (g.startIndex s + j) :=
        (g.lt_p_succ_startIndex haN).trans_le (g.p_mono (by omega) hlt.1.le)
      rw [max_eq_left hgt.le, min_eq_left hlt.2.le]
      exact (hwa.mono (ℱ.mono hgt.le)).mul hξ
/-- The integrand of the weighted increment, as a sum over the pieces meeting `(s, t]`. -/
lemma eval_incr_eq (σ : ℝ) (e : E) (ω : Ω) :
    (G.incr w hw hwm s t hs hst).eval σ e ω
      = ∑ j ∈ Finset.range (g.clampIndex t - g.startIndex s),
        (Set.Ioc (min (max (g.p (g.startIndex s + j)) s) t)
          (min (max (g.p (g.startIndex s + (j + 1))) s) t)).indicator (fun _ => (1 : ℝ)) σ
        * ∑ k, (w ω * G.ξ (g.startIndex s + j) k ω) * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
  unfold eval
  change ∑ i ∈ Finset.range (g.clampIndex t - g.startIndex s + 1),
      (Set.Ioc ((g.incr s t hs hst).p i) ((g.incr s t hs hst).p (i + 1))).indicator
        (fun _ => (1 : ℝ)) σ
      * ∑ k, (if i = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (i - 1)) k ω)
        * (G.B k).indicator (fun _ => (1 : ℝ)) e = _
  rw [Finset.sum_range_succ']
  simp only [if_true, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g.incr_p_succ, g.incr_p_succ]
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


