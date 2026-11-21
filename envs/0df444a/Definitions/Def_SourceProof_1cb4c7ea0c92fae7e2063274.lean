-- Prove2me | Definitions.Def_SourceProof_1cb4c7ea0c92fae7e2063274
-- name    : SourceProof_1cb4c7ea0c92fae7e2063274
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:45.236807+00:00
-- url     : https://prove2.me/theorems/df639ed3-d415-45dc-9730-39b7f559916d
-- title:
--   LevyStochCalc source module: SourceProof_1cb4c7ea0c92fae7e2063274
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le` comes from the `LevyStochCalc.Brownian.CrossOrthogonalityLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000
import Definitions.Def_SourceProof_a4d1770441285d17727a5c0a

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


theorem _root_.Prove2MeSourceProof.h_1cb4c7ea0c92fae7e2063274 (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  have hΔ : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (x y : ℝ), Measurable fun ω => V.W y ω - V.W x ω :=
    fun V x y => (V.measurable_eval y).sub (V.measurable_eval x)
  have hΔℱ : ∀ (k : Fin d) {x y s : ℝ}, x ≤ s → y ≤ s →
      Measurable[ℱ s] fun ω => (W.W k).W y ω - (W.W k).W x ω := fun k x y s hxs hys =>
    (((hcoord k).measurable y).mono (ℱ.mono hys) le_rfl).sub
      (((hcoord k).measurable x).mono (ℱ.mono hxs) le_rfl)
  have hξη : StronglyMeasurable[ℱ r] fun ω => ξ ω * η ω := (hξ.mono (ℱ.mono hpr)).mul hη
  have hξηb : ∀ ω, |ξ ω * η ω| ≤ |Mξ| * |Mη| := fun ω => by
    rw [abs_mul]
    exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  rcases le_or_gt q r with hqr | hrq
  · -- the `Wⁱ` increment is already known at time `r`
    have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W p ω) * η ω :=
      ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr hqr).stronglyMeasurable).mul hη
    have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
      ((hξm.mul (hΔ (W.W i) p q)).mul hηm)
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- split the `Wⁱ` increment at `r`
    have hsplit : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
          * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
        = fun ω => (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω))
          + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) := by
      funext ω; ring
    rw [hsplit,
      integral_add (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term (W.W i) (W.W j) hp hpr hr hrv.le hξm hηm hξb hηb)
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term (W.W i) (W.W j) hr hrq.le hr hrv.le hξm hηm hξb hηb)]
    have h1 : ∫ ω, (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
        * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
      have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W r ω - (W.W i).W p ω) * η ω :=
        ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr le_rfl).stronglyMeasurable).mul hη
      have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
        ((hξm.mul (hΔ (W.W i) p r)).mul hηm)
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, zero_add]
    -- both increments now start at `r`
    rcases lt_trichotomy q v with hqv | rfl | hvq
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))
            + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
                * ((W.W j).W v ω - (W.W j).W q ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term (W.W i) (W.W j) hr hrq.le hr hrq.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          * ((W.W j).W v ω - (W.W j).W q ω)) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term (W.W i) (W.W j) hr hrq.le (hr.trans hrq.le) hqv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        _root_.Prove2MeSourceProof.h_a4d1770441285d17727a5c0a W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) (hr.trans hrq.le) hqv
          (Y := fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          (((hξ.mono (ℱ.mono (hpr.trans hrq.le))).mul
            (hΔℱ i hrq.le le_rfl).stronglyMeasurable).mul (hη.mono (ℱ.mono hrq.le)))
          ((hξm.mul (hΔ (W.W i) r q)).mul hηm), add_zero]
    · have heq : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W q ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
              * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω)) := by
        funext ω; ring
      rw [heq]
      exact _root_.Prove2MeSourceProof.h_a4d1770441285d17727a5c0a W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))
            + (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
                * ((W.W i).W q ω - (W.W i).W v ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term (W.W i) (W.W j) hr hrv.le hr hrv.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          * ((W.W i).W q ω - (W.W i).W v ω)) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term (W.W i) (W.W j) (hr.trans hrv.le) hvq.le hr hrv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        _root_.Prove2MeSourceProof.h_a4d1770441285d17727a5c0a W hij hcoord hr hrv hξη (hξm.mul hηm) hξηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W i) (hcoord i) (hr.trans hrv.le) hvq
          (Y := fun ω => ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          (((hξ.mono (ℱ.mono (hpr.trans hrv.le))).mul (hη.mono (ℱ.mono hrv.le))).mul
            (hΔℱ j hrv.le le_rfl).stronglyMeasurable)
          ((hξm.mul hηm).mul (hΔ (W.W j) r v)), add_zero]
end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


