-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F000
-- name    : LevyStochCalc_Poisson_MarkStepWeight_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:37:36.158236+00:00
-- url     : https://prove2.me/theorems/faf38d65-2bf1-42a0-813b-e3ac7c1c8f2b
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepWeight
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepWeight. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIsometry_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums, negations and weightings of mark-step integrands

Two mark-step integrands on a common time grid are added by concatenating their mark
families (`MarkStep.append`), and a mark-step integrand is negated coefficientwise
(`MarkStep.neg`); both operations act additively on the compensated integral and on the
integrand, so the `L²` isometry applies to differences. Multiplying the coefficients from a
given piece on by a bounded measurable weight `w`, and zeroing the earlier ones
(`MarkStep.weight`), yields the isometry for the weighted increment of the integral over a
grid interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The sum of two mark-step integrands on a common grid, by concatenating their marks. -/
def append (G G' : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K + G'.K
  B := Fin.append G.B G'.B
  B_measurable := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_measurable k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_measurable k) k
  B_finite := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_finite k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_finite k) k
  ξ := fun i => Fin.append (G.ξ i) (G'.ξ i)
  ξ_bounded := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_bounded i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_bounded i k) k
  ξ_measurable := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_measurable i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_measurable i k) k
/-- The negative of a mark-step integrand. -/
def neg (G : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => -G.ξ i k ω
  ξ_bounded := fun i k => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    exact ⟨M, fun ω => by rw [abs_neg]; exact hM ω⟩
  ξ_measurable := fun i k => (G.ξ_measurable i k).neg
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

lemma integral_append (t : ℝ) (ω : Ω) :
    (G.append G').integral N t ω = G.integral N t ω + G'.integral N t ω := by
  unfold integral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)
        ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
lemma full_append (ω : Ω) : (G.append G').full N ω = G.full N ω + G'.full N ω := by
  unfold full
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
lemma eval_append (s : ℝ) (e : E) (ω : Ω) :
    (G.append G').eval s e ω = G.eval s e ω + G'.eval s e ω := by
  unfold eval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add]
  congr 1
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * (Fin.append G.B G'.B k).indicator (fun _ => (1 : ℝ)) e = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
lemma Adapted.append {G G' : MarkStep Ω E ν g}
    (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) : (G.append G').Adapted ℱ := by
  intro i hi k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.castAdd _ k))
    rw [Fin.append_left]
    exact hG i hi k
  · change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.natAdd _ k))
    rw [Fin.append_right]
    exact hG' i hi k
lemma integral_neg (t : ℝ) (ω : Ω) : G.neg.integral N t ω = -G.integral N t ω := by
  unfold integral
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω)
  exact neg_mul _ _
lemma full_neg (ω : Ω) : G.neg.full N ω = -G.full N ω := by
  unfold full
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω)
  exact neg_mul _ _
lemma eval_neg (s : ℝ) (e : E) (ω : Ω) : G.neg.eval s e ω = -G.eval s e ω := by
  unfold eval
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
    = -(G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e)
  exact neg_mul _ _
lemma Adapted.neg {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ) :
    G.neg.Adapted ℱ := fun i hi k => (hG i hi k).neg
include hℱ in
/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, is the `L²` distance of the integrands. -/
theorem integral_sub_sq_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (G.integral N t ω - G'.integral N t ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := (G.append G'.neg).integral_sq_at N hℱ (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key
include hℱ in
/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sub_sq_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω - G'.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  have key := (G.append G'.neg).lintegral_integral_sq_at N hℱ (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key
end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The mark-step integrand whose coefficients on the pieces from index `a` on are
multiplied by a bounded measurable weight `w`, and whose earlier coefficients vanish. -/
def weight (G : MarkStep Ω E ν g) (w : Ω → ℝ) (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C)
    (hwm : Measurable w) (a : ℕ) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => if a ≤ i then w ω * G.ξ i k ω else 0
  ξ_bounded := fun i k => by
    obtain ⟨C, hC⟩ := hw
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    refine ⟨|C| * |M|, fun ω => ?_⟩
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul ((hC ω).trans (le_abs_self C)) ((hM ω).trans (le_abs_self M))
        (abs_nonneg _) (abs_nonneg _)
    · rw [abs_zero]
      positivity
  ξ_measurable := fun i k => by
    by_cases h : a ≤ i
    · simp only [h, if_true]
      exact hwm.mul (G.ξ_measurable i k)
    · simp only [h, if_false]
      exact measurable_const
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)

include hw hwm in
lemma Adapted.weight {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ)
    {a : ℕ} (hwa : @StronglyMeasurable Ω ℝ _ (ℱ (g.p a)) w) :
    (G.weight w hw hwm a).Adapted ℱ := by
  intro i hi k
  change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
    (fun ω => if a ≤ i then w ω * G.ξ i k ω else 0)
  by_cases h : a ≤ i
  · simp only [h, if_true]
    exact (hwa.mono (ℱ.mono (g.p_mono h hi.le))).mul (hG i hi k)
  · simp only [h, if_false]
    exact stronglyMeasurable_const
end Weight

end MarkStep

end LevyStochCalc.Poisson.Compensated


