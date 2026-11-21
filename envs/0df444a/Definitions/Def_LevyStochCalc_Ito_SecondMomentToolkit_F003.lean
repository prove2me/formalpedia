-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F003
-- name    : LevyStochCalc_Ito_SecondMomentToolkit_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:24:13.193553+00:00
-- url     : https://prove2.me/theorems/65fb539a-b50f-4d23-a900-280cb12ff68d
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentToolkit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentToolkit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F001

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

end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}

end Running

section Polarised

omit [IsProbabilityMeasure P] in
/-- The energy of a square-integrable integrand on a window is the integral of its square for the
product measure. -/
theorem toReal_lintegral_sq_eq {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
      = ∫ p, f p.1 p.2 * f p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hmeas : Measurable fun p : Ω × ℝ => (‖f p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    hf.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [integral_mul_self_eq_toReal (memLp_two_prod hf hfq)]
  congr 1
  exact (lintegral_prod _ hmeas.aemeasurable).symm
end Polarised

section PolarisedDrift

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment


