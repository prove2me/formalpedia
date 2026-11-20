-- Prove2me | Definitions.Def_BrownianMotion_Gaussian_Moment_F000
-- name    : BrownianMotion_Gaussian_Moment_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:07:56.131419+00:00
-- url     : https://prove2.me/theorems/a7efd6ec-d0c1-490f-b827-30ad7fb6a7a7
-- title:
--   Source declarations: BrownianMotion.Gaussian.Moment
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Gaussian.Moment. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_76a6083be786724fac218630
import Mathlib.Probability.Distributions.Gaussian.Real


@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

lemma centralMoment_fun_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) :=
  _root_.Prove2MeSourceProof.h_76a6083be786724fac218630 ..
end ProbabilityTheory


