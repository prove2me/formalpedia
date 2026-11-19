-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F001
-- name    : LevyStochCalc_Brownian_DriftIncrement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:42:07.932689+00:00
-- url     : https://prove2.me/theorems/ca1f38b1-f62e-4bb3-93da-e642f171b7b0
-- title:
--   Source declarations: LevyStochCalc.Brownian.DriftIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.DriftIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_DriftIncrement_F000
import Definitions.Def_SourceProof_0c7e85b4037c170c4bb0381a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments of the integral of a bounded function

The drift part of an Itô process is `t ↦ ∫_0^t b_s ds`. Its increment across a cell is the
integral over that cell, and is bounded by the bound on `b` times the cell length.

## Main statements

* `LevyStochCalc.integrableOn_of_bounded_of_measurable` — a bounded measurable function is
  integrable on any set of finite measure.
* `LevyStochCalc.setIntegral_Icc_sub_Icc` — `∫_{[0,b]} − ∫_{[0,a]} = ∫_{(a,b]}`.
* `LevyStochCalc.abs_setIntegral_Ioc_le` — `|∫_{(a,b]} f| ≤ B·(b − a)`.
* `LevyStochCalc.abs_setIntegral_Icc_sub_le` — `t ↦ ∫_{[0,t]} f` is `B`-Lipschitz.
* `LevyStochCalc.continuous_setIntegral_Icc` — hence continuous.
* `LevyStochCalc.measurable_setIntegral` — the integral over a fixed set is measurable in
  the parameter.
* `LevyStochCalc.measurable_setIntegral_Ioc` — the window integral is measurable in the
  parameter.
-/

namespace LevyStochCalc

open MeasureTheory

/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
/-- The integral of a jointly measurable function over a fixed window is measurable in the
parameter. -/
theorem measurable_setIntegral_Ioc {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (a b : ℝ) :
    Measurable fun ω => ∫ s in Set.Ioc a b, f ω s ∂volume :=
  measurable_setIntegral hf (Set.Ioc a b)
/-- The integral of a bounded function over `[0, t]` is `B`-Lipschitz in `t`. -/
theorem abs_setIntegral_Icc_sub_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) (t t' : ℝ) :
    |(∫ s in Set.Icc (0 : ℝ) t', f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume|
      ≤ B * |t' - t| := by
  have hIcc : ∀ u : ℝ, 0 ≤ u →
      (∫ s in Set.Icc (0 : ℝ) u, f s ∂volume) = ∫ s in Set.Ioc (0 : ℝ) u, f s ∂volume := by
    intro u _
    rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have hempty : ∀ u : ℝ, u < 0 → (∫ s in Set.Icc (0 : ℝ) u, f s ∂volume) = 0 := by
    intro u hu
    rw [Set.Icc_eq_empty (not_le.mpr hu), MeasureTheory.setIntegral_empty]
  have key : ∀ a b : ℝ, a ≤ b →
      |(∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume|
        ≤ B * (b - a) := by
    intro a b hab
    rcases lt_or_ge b 0 with hb | hb
    · rw [hempty b hb, hempty a (lt_of_le_of_lt hab hb)]
      simpa using mul_nonneg hB0 (by linarith)
    · rcases lt_or_ge a 0 with ha | ha
      · rw [hempty a ha, sub_zero, hIcc b hb]
        refine le_trans (_root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a hf hB hb) ?_
        have : (0 : ℝ) ≤ -a := by linarith
        nlinarith
      · rw [setIntegral_Icc_sub_Icc hf hB ha hab]
        exact _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a hf hB hab
  rcases le_total t t' with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t' - t)]
    exact key t t' h
  · rw [abs_sub_comm ((∫ s in Set.Icc (0 : ℝ) t', f s ∂volume)),
      abs_sub_comm t' t, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - t')]
    exact key t' t h
/-- The integral of a bounded measurable function over `[0, t]` is continuous in `t`. -/
theorem continuous_setIntegral_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  have hlip : LipschitzWith (Real.toNNReal B)
      fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
    refine LipschitzWith.of_dist_le_mul fun t t' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal B hB0]
    exact abs_setIntegral_Icc_sub_le hf hB0 hB t' t
  exact hlip.continuous
end LevyStochCalc


