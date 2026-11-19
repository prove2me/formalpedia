-- Prove2me | Definitions.Def_SourceProof_8fe1606d2a5bd9c8ee5cbf20
-- name    : SourceProof_8fe1606d2a5bd9c8ee5cbf20
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:01:51.882189+00:00
-- url     : https://prove2.me/theorems/0ed8d35a-f4cf-4cd1-8ac3-7af3c142f6eb
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.integral_mul_setIntegral_Ioc
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing an integrable weight against a time integral

For an integrable weight and a bounded jointly measurable process on a bounded time interval, the
expectation of the weight against the time integral of the process is the time integral of the
expectations.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]


theorem _root_.Prove2MeSourceProof.h_8fe1606d2a5bd9c8ee5cbf20 {a t : ℝ} {Z : Ω → ℂ} (hZm : Measurable Z)
    (hZ : Integrable Z P) {Φ : Ω → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ))
    {C : ℝ} (hC : ∀ ω u, ‖Φ ω u‖ ≤ C) :
    ∫ ω, Z ω * (∫ u in Set.Ioc a t, Φ ω u) ∂P
      = ∫ u in Set.Ioc a t, (∫ ω, Z ω * Φ ω u ∂P) := by
  have hmeas : Measurable (Function.uncurry fun ω u => Z ω * Φ ω u) :=
    (hZm.comp measurable_fst).mul hΦ
  have hmaj : Integrable (fun p : Ω × ℝ => ‖Z p.1‖ * C)
      (P.prod (volume.restrict (Set.Ioc a t))) :=
    hZ.norm.mul_prod (integrable_const C)
  have hprod : Integrable (Function.uncurry fun ω u => Z ω * Φ ω u)
      (P.prod (volume.restrict (Set.Ioc a t))) := by
    refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    calc ‖Z p.1 * Φ p.1 p.2‖ = ‖Z p.1‖ * ‖Φ p.1 p.2‖ := norm_mul _ _
      _ ≤ ‖Z p.1‖ * C := by
          exact mul_le_mul_of_nonneg_left (hC _ _) (norm_nonneg _)
  calc ∫ ω, Z ω * (∫ u in Set.Ioc a t, Φ ω u) ∂P
      = ∫ ω, (∫ u in Set.Ioc a t, Z ω * Φ ω u) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (integral_const_mul (Z ω) fun u => Φ ω u).symm
    _ = ∫ u in Set.Ioc a t, (∫ ω, Z ω * Φ ω u ∂P) := integral_integral_swap hprod
section Swap

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]

end Swap

end LevyStochCalc.Probability


