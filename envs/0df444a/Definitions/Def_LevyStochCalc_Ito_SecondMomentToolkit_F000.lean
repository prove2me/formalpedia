-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F000
-- name    : LevyStochCalc_Ito_SecondMomentToolkit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:38.324508+00:00
-- url     : https://prove2.me/theorems/a0811a0a-c98b-4282-9f3d-b4ab65fb1266
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentToolkit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentToolkit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

omit [IsProbabilityMeasure P] in
/-- The integral of the square of a square-integrable function is the real part of its
energy. -/
theorem integral_mul_self_eq_toReal {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, f ω * f ω ∂P = (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => mul_self_nonneg _)
    (hf.aestronglyMeasurable.mul hf.aestronglyMeasurable)]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← sq, show ((‖f ω‖₊ : ℝ≥0∞)) = ‖f ω‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
omit [IsProbabilityMeasure P] in
/-- The energy of a square-integrable function is finite. -/
theorem lintegral_sq_lt_top_of_memLp_two {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  have h := (hf.integrable_mul hf).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h
  refine lt_of_eq_of_lt ?_ h
  refine lintegral_congr fun ω => ?_
  rw [Pi.mul_apply, enorm_mul, sq]
  rfl
omit [IsProbabilityMeasure P] in
/-- The square of a sum of two square-integrable functions, under the integral. -/
theorem integral_mul_self_add {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, (f ω + g ω) * (f ω + g ω) ∂P
      = ∫ ω, f ω * f ω ∂P + 2 * ∫ ω, f ω * g ω ∂P + ∫ ω, g ω * g ω ∂P := by
  have hff : Integrable (fun ω => f ω * f ω) P := hf.integrable_mul hf
  have hfg : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have hgg : Integrable (fun ω => g ω * g ω) P := hg.integrable_mul hg
  have hexp : (fun ω => (f ω + g ω) * (f ω + g ω))
      = fun ω => f ω * f ω + (2 : ℝ) * (f ω * g ω) + g ω * g ω := by
    funext ω
    ring
  have h2 : Integrable (fun ω => (2 : ℝ) * (f ω * g ω)) P := hfg.const_mul 2
  have h12 : Integrable (fun ω => f ω * f ω + (2 : ℝ) * (f ω * g ω)) P := hff.add h2
  rw [hexp, integral_add h12 hgg, integral_add hff h2, integral_const_mul]
end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}

end Running

section Polarised

end Polarised

section PolarisedDrift

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment


