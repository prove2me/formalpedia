-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000
-- name    : LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:10:53.883018+00:00
-- url     : https://prove2.me/theorems/f63a6356-fa35-44ab-a20f-32845166cd80
-- title:
--   Source declarations: LevyStochCalc.Brownian.CrossOrthogonalityLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CrossOrthogonalityLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001
import Definitions.Def_SourceProof_0d5475ecda5b11387d030812

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

/-- Clamping an interval to `(-∞, t]` either collapses it or leaves its left endpoint alone. -/
lemma min_eq_or_lt_min {p q : ℝ} (h : p < q) (t : ℝ) :
    min p t = min q t ∨ (min p t = p ∧ p < min q t) := by
  rcases lt_or_ge t q with htq | hqt
  · rcases lt_or_ge p t with hpt | htp
    · exact Or.inr ⟨min_eq_left hpt.le, by rw [min_eq_right htq.le]; exact hpt⟩
    · exact Or.inl (by rw [min_eq_right htp, min_eq_right htq.le])
  · exact Or.inr ⟨min_eq_left (h.le.trans hqt), by rw [min_eq_left hqt]; exact h⟩
/-- The square of a Brownian increment over a possibly degenerate interval is integrable. -/
lemma integrable_increment_sq (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    Integrable (fun ω => (V.W q ω - V.W p ω) ^ 2) P := by
  rcases eq_or_lt_of_le hpq with h | h
  · have hz : (fun ω => (V.W q ω - V.W p ω) ^ 2) = fun _ => (0 : ℝ) := by
      funext ω; rw [← h]; simp
    rw [hz]
    exact integrable_zero Ω ℝ P
  · exact _root_.Prove2MeSourceProof.h_0d5475ecda5b11387d030812 V hp h
/-- A product of two bounded coefficients and two Brownian increments is integrable. -/
lemma integrable_cross_term (V₁ V₂ : BrownianMotion P) {p q r v : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hr : 0 ≤ r) (hrv : r ≤ v) {ξ η : Ω → ℝ} (hξm : Measurable ξ) (hηm : Measurable η)
    {Mξ Mη : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω))
      * (η ω * (V₂.W v ω - V₂.W r ω))) P := by
  have hm1 : Measurable fun ω => V₁.W q ω - V₁.W p ω :=
    (V₁.measurable_eval q).sub (V₁.measurable_eval p)
  have hm2 : Measurable fun ω => V₂.W v ω - V₂.W r ω :=
    (V₂.measurable_eval v).sub (V₂.measurable_eval r)
  have hprod : Integrable (fun ω => (V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) P := by
    have hdom : Integrable (fun ω => 1 / 2 * (V₁.W q ω - V₁.W p ω) ^ 2
        + 1 / 2 * (V₂.W v ω - V₂.W r ω) ^ 2) P :=
      ((integrable_increment_sq V₁ hp hpq).const_mul (1 / 2 : ℝ)).add
        ((integrable_increment_sq V₂ hr hrv).const_mul (1 / 2 : ℝ))
    refine Integrable.mono' hdom (hm1.mul hm2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (V₁.W q ω - V₁.W p ω), sq_abs (V₂.W v ω - V₂.W r ω),
      sq_nonneg (|V₁.W q ω - V₁.W p ω| - |V₂.W v ω - V₂.W r ω|)]
  have heq : (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω)) * (η ω * (V₂.W v ω - V₂.W r ω)))
      = fun ω => (ξ ω * η ω) * ((V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) := by
    funext ω; ring
  rw [heq]
  refine Integrable.bdd_mul (c := |Mξ| * |Mη|) hprod (hξm.mul hηm).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)
end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


