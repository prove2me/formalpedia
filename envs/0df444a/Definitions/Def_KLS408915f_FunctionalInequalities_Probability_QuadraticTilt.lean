-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
-- name    : KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:40:28.428748+00:00
-- url     : https://prove2.me/theorems/74a06053-0b3f-46e3-b09a-1620a6cba443
-- title:
--   Nonnegative quadratic tilts
-- statement:
--   For a probability measure $\mu$ and $\delta\ge0$, `isProbabilityMeasure_quadraticTilt` states that the tilt by $e^{-\delta\|x\|^2/2}$ is again a probability measure. `quadraticTiltLaw` packages this tilted measure as a `ProbabilityMeasure`; no convergence assertion is included in this bundle.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L97-L116 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, definition bundle `KLS408915f_FunctionalInequalities_Probability_QuadraticTilt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open MeasureTheory Filter Topology Set
namespace FunctionalInequalities
namespace Probability
section Laws
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
omit [NormedSpace ℝ E] in
/-- The quadratic tilt of a probability measure is a probability measure for `δ ≥ 0`. -/
theorem isProbabilityMeasure_quadraticTilt (μ : Measure E) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    IsProbabilityMeasure (μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) := by
  apply MeasureTheory.isProbabilityMeasure_tilted
  refine (integrable_const (1 : ℝ)).mono' ?_ ?_
  · exact (show Continuous (fun x : E => Real.exp (-(δ / 2) * ‖x‖ ^ 2)) by
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hδ (by norm_num))) (sq_nonneg _))
omit [NormedSpace ℝ E] in
/-- The normalized quadratic tilt `e^{-δ‖x‖²/2} μ / Z_δ` as a probability law. -/
def quadraticTiltLaw (μ : ProbabilityMeasure E) (δ : ℝ) (hδ : 0 ≤ δ) :
    ProbabilityMeasure E :=
  ⟨(μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2),
    isProbabilityMeasure_quadraticTilt (μ : Measure E) δ hδ⟩
end Laws
end Probability
end FunctionalInequalities


