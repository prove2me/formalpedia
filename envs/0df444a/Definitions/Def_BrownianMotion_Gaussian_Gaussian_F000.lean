-- Prove2me | Definitions.Def_BrownianMotion_Gaussian_Gaussian_F000
-- name    : BrownianMotion_Gaussian_Gaussian_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:08:54.993598+00:00
-- url     : https://prove2.me/theorems/2d223f56-cf74-4415-a23c-ba64472b92f9
-- title:
--   Source declarations: BrownianMotion.Gaussian.Gaussian
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Gaussian.Gaussian, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic


@[expose] public section

/-!
# Facts about Gaussian characteristic function
-/

open Complex MeasureTheory WithLp NormedSpace

open scoped Matrix NNReal Real InnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

set_option backward.isDefEq.respectTransparency false in
lemma HasGaussianLaw.charFun_map_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (h : HasGaussianLaw X P) (t : ℝ) :
    charFun (P.map X) t = cexp (t * P[X] * I - t ^ 2 * Var[X; P] / 2) := by
  rw [h.map_eq_gaussianReal, IsGaussian.charFun_eq', covarianceBilin_real_self]
  simp [variance_nonneg, integral_complex_ofReal, mul_comm]
end ProbabilityTheory


