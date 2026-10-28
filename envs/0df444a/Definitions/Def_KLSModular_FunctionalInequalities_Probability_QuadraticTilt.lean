-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt
-- name    : KLSModular_FunctionalInequalities_Probability_QuadraticTilt
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:19:13.164978+00:00
-- url     : https://prove2.me/theorems/60d2b9ef-6970-4c75-8c09-768a09afafb4
-- title:
--   Nonnegative quadratic tilts
-- statement:
--   For a probability measure $\mu$ and $\delta\ge0$, `isProbabilityMeasure_quadraticTilt` states that the tilt by $e^{-\delta\|x\|^2/2}$ is again a probability measure. `quadraticTiltLaw` packages this tilted measure as a `ProbabilityMeasure`; no convergence assertion is included in this bundle.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.MeasureTheory.Integral.DominatedConvergence
--   import Mathlib.Analysis.SpecialFunctions.Exp
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import Mathlib.Probability.Moments.Covariance
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Topology.Algebra.Module.FiniteDimension
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def quadraticTiltLaw (μ : ProbabilityMeasure E) (δ : ℝ) (hδ : 0 ≤ δ) :
--       ProbabilityMeasure E :=
--     ⟨(μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2),
--       isProbabilityMeasure_quadraticTilt (μ : Measure E) δ hδ⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc).
--
--   Theorems in source order:
--
--   - [`integral_quadraticTilt_tendsto`](https://prove2.me/theorems/ffe92b60-eb22-4bf2-b690-535d392b8556)
--   - [`inner_covariance_quadraticTilt_tendsto`](https://prove2.me/theorems/ce081f02-1f45-416f-82f0-2ad61ab09ec7)
--   - [`covariance_quadraticTilt_tendsto`](https://prove2.me/theorems/34f101b3-ed51-49ba-ad65-9df453ba5bd4)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean) · `FunctionalInequalities.Probability.QuadraticTilt` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L97-L116 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, definition bundle `KLSModular_FunctionalInequalities_Probability_QuadraticTilt`; the repository is private at upload time).

import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.Normed.Module.FiniteDimension
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


