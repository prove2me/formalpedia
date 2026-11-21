-- Prove2me | Definitions.Def_SourceProof_d48a4c705b920c2354300189
-- name    : SourceProof_d48a4c705b920c2354300189
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:51:53.167958+00:00
-- url     : https://prove2.me/theorems/18f8f363-0bd0-4132-bf6d-971a450af353
-- title:
--   LevyStochCalc source module: SourceProof_d48a4c705b920c2354300189
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` comes from the `LevyStochCalc.Poisson.MarkStepPolarised` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_MarkStepPolarised_F000

open private triple_integrable from Definitions.Def_LevyStochCalc_Poisson_MarkStepPolarised_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear form of the `L²` isometry for mark-step integrands

For two adapted mark-step integrands `G, G'` on a common time grid, the expectation of the
product of their compensated integrals up to a time `t ≥ 0` is the expectation of the time-mark
integral of the product of the integrands,
`E[(∫_0^t ∫_E G dÑ)(∫_0^t ∫_E G' dÑ)] = E[∫_E ∫_0^t G(s, e) G'(s, e) ds ν(de)]`, and the same
identity holds for the integrals over the whole horizon. It comes from the isometry for a
difference applied to the pairs `G, G'` and `G, G'.neg`, together with the polarisation identity
`4 a a' = (a + a') ^ 2 - (a - a') ^ 2`. Splitting the nested integral of that identity into its
two halves uses the boundedness of a mark-step integrand and the finite intensity of its mark
sets.

## Main statements

* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` — the bilinear identity up to a
  time `t ≥ 0`.
* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_full_mul` — the bilinear identity for the
  integrals over the whole horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Polarisation

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (hℱ : IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_d48a4c705b920c2354300189 (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, G.integral N t ω * G'.integral N t ω ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by
  classical
  -- the two isometries, for the sum and for the difference
  have hminus := LevyStochCalc.Poisson.Compensated.MarkStep.integral_sub_sq_at N hℱ G G' hG hG' ht
  have hplus := LevyStochCalc.Poisson.Compensated.MarkStep.integral_sub_sq_at N hℱ G G'.neg hG hG'.neg ht
  simp only [LevyStochCalc.Poisson.Compensated.MarkStep.integral_neg, LevyStochCalc.Poisson.Compensated.MarkStep.eval_neg, sub_neg_eq_add] at hplus
  -- the left-hand sides combine by polarisation
  have hiA : Integrable (fun ω => (G.integral N t ω + G'.integral N t ω) ^ 2) P := by
    have h := (LevyStochCalc.Poisson.Compensated.MarkStep.memLp_integral N (G.append G') t).integrable_sq
    simp only [LevyStochCalc.Poisson.Compensated.MarkStep.integral_append] at h
    exact h
  have hiD : Integrable (fun ω => (G.integral N t ω - G'.integral N t ω) ^ 2) P := by
    have h := (LevyStochCalc.Poisson.Compensated.MarkStep.memLp_integral N (G.append G'.neg) t).integrable_sq
    simp only [LevyStochCalc.Poisson.Compensated.MarkStep.integral_append, LevyStochCalc.Poisson.Compensated.MarkStep.integral_neg, ← sub_eq_add_neg] at h
    exact h
  have hlhs : ∫ ω, (G.integral N t ω + G'.integral N t ω) ^ 2 ∂P
      - ∫ ω, (G.integral N t ω - G'.integral N t ω) ^ 2 ∂P
      = 4 * ∫ ω, G.integral N t ω * G'.integral N t ω ∂P := by
    rw [← integral_sub hiA hiD, show (fun ω => (G.integral N t ω + G'.integral N t ω) ^ 2
        - (G.integral N t ω - G'.integral N t ω) ^ 2)
      = fun ω => 4 * (G.integral N t ω * G'.integral N t ω) from funext fun ω => by ring,
      integral_const_mul]
  -- the right-hand sides combine by splitting the nested integral
  obtain ⟨C₁, hC₁⟩ := G.eval_bounded
  obtain ⟨C₂, hC₂⟩ := G'.eval_bounded
  set S : Set E := (⋃ k, G.B k) ∪ ⋃ k, G'.B k with hSdef
  have hS : MeasurableSet S := G.measurableSet_iUnion_B.union G'.measurableSet_iUnion_B
  have hSfin : ν S ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨G.measure_iUnion_B_ne_top, G'.measure_iUnion_B_ne_top⟩)
    (measure_union_le _ _)
  have hzero : ∀ ω s e, e ∉ S → G.eval s e ω = 0 ∧ G'.eval s e ω = 0 := by
    intro ω s e he
    exact ⟨G.eval_support ω s e fun hk => he (Or.inl hk),
      G'.eval_support ω s e fun hk => he (Or.inr hk)⟩
  have hbound : ∀ (σ : ℝ), |σ| = 1 → ∀ ω s e,
      |(G.eval s e ω + σ * G'.eval s e ω) ^ 2| ≤ (|C₁| + |C₂|) ^ 2 := by
    intro σ hσ ω s e
    have h1 : |G.eval s e ω| ≤ |C₁| := (hC₁ ω s e).trans (le_abs_self _)
    have h2 : |σ * G'.eval s e ω| ≤ |C₂| := by
      rw [abs_mul, hσ, one_mul]
      exact (hC₂ ω s e).trans (le_abs_self _)
    have h3 : |G.eval s e ω + σ * G'.eval s e ω| ≤ |C₁| + |C₂| :=
      (abs_add_le _ _).trans (add_le_add h1 h2)
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (G.eval s e ω + σ * G'.eval s e ω),
      sq_abs (G.eval s e ω + σ * G'.eval s e ω), abs_nonneg C₁, abs_nonneg C₂]
  have hmeasG : Measurable fun q : Ω × ℝ × E => G.eval q.2.1 q.2.2 q.1 := G.eval_measurable
  have hmeasG' : Measurable fun q : Ω × ℝ × E => G'.eval q.2.1 q.2.2 q.1 := G'.eval_measurable
  obtain ⟨hp1, hp2, hp3⟩ := triple_integrable (T := t) (P := P)
    (fun ω s e => (G.eval s e ω + G'.eval s e ω) ^ 2)
    ((hmeasG.add hmeasG').pow_const 2) (sq_nonneg _)
    (fun ω s e => by simpa using hbound 1 (by norm_num) ω s e) hS hSfin
    (fun ω s e he => by
      obtain ⟨ha, hb⟩ := hzero ω s e he
      rw [ha, hb]; ring)
  obtain ⟨hm1, hm2, hm3⟩ := triple_integrable (T := t) (P := P)
    (fun ω s e => (G.eval s e ω - G'.eval s e ω) ^ 2)
    ((hmeasG.sub hmeasG').pow_const 2) (sq_nonneg _)
    (fun ω s e => by
      have h := hbound (-1) (by norm_num) ω s e
      simpa [sub_eq_add_neg] using h) hS hSfin
    (fun ω s e he => by
      obtain ⟨ha, hb⟩ := hzero ω s e he
      rw [ha, hb]; ring)
  have hp1' : ∀ ω e, Integrable (fun s => (G.eval s e ω + G'.eval s e ω) ^ 2)
    (volume.restrict (Set.Icc (0 : ℝ) t)) := hp1
  have hp2' : ∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω + G'.eval s e ω) ^ 2 ∂volume) ν := hp2
  have hp3' : Integrable (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω + G'.eval s e ω) ^ 2 ∂volume ∂ν) P := hp3
  have hm1' : ∀ ω e, Integrable (fun s => (G.eval s e ω - G'.eval s e ω) ^ 2)
    (volume.restrict (Set.Icc (0 : ℝ) t)) := hm1
  have hm2' : ∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume) ν := hm2
  have hm3' : Integrable (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) P := hm3
  have hrhs : (∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
        (G.eval s e ω + G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P)
      - ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
        (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P
      = 4 * ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
        G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by
    rw [← integral_sub hp3' hm3', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    rw [← integral_sub (hp2' ω) (hm2' ω), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
    simp only []
    rw [← integral_sub (hp1' ω e) (hm1' ω e), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    ring
  rw [hplus, hminus] at hlhs
  rw [hrhs] at hlhs
  linarith [hlhs]
end Polarisation

end MarkStep

end LevyStochCalc.Poisson.Compensated


