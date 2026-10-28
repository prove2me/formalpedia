-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:54:51.572871+00:00
-- url     : https://prove2.me/theorems/eabcdc52-c914-4c59-b1af-3d43455f910d
-- title:
--   Gaussian–quadratic regularization sequences
-- statement:
--   `tiltRate k` is the positive rate $\delta_k=1/(k+1)$, `gaussianSeq μ n` is the Gaussian smoothing of $\mu$ with inverse-variance parameter $n+1$, and `rowLaw μ n k` applies the quadratic tilt of rate $\delta_k$. Given a Borell density, `regularSeq` packages the probability law associated with the regular potential obtained from the same smoothing and tilt parameters. `statistics` records the mean, raw second moment, and covariance operator of a probability law.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Regular
--   import FunctionalInequalities.Probability.QuadraticTilt
--   import FunctionalInequalities.Analysis.DiagonalSelector
--   import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def tiltRate (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8), [`KLS/LogConcave/Density/GaussianSmoothing/Approximation`](https://prove2.me/theorems/d5560108-f34d-426e-87a5-851045a6e923), [`KLS/LogConcave/Density/GaussianSmoothing/Regular`](https://prove2.me/theorems/d0116214-37fa-4895-a2c9-05d0dd946cde), [`Probability/QuadraticTilt`](https://prove2.me/theorems/60d2b9ef-6970-4c75-8c09-768a09afafb4), [`Analysis/DiagonalSelector`](https://prove2.me/theorems/7adcdbd1-7f86-49e3-a792-dc6701cfeaf2).
--
--   Theorems in source order:
--
--   - [`row_joint_tendsto`](https://prove2.me/theorems/23822530-689b-4fdf-a9f4-e7013d658d1f)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation.lean#L31-L163 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_DiagonalSelector
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis
noncomputable section
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The quadratic-tilt rates `δ_k = 1/(k+1)`. -/
def tiltRate (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
theorem tiltRate_pos (k : ℕ) : 0 < tiltRate k := by unfold tiltRate; positivity
/-- The Gaussian smoothings `μ * γ_{n+1}` as probability laws. -/
def gaussianSeq (μ : ProbabilityMeasure E) (n : ℕ) : ProbabilityMeasure E :=
  smoothedProbabilityLaw μ ((n : ℝ) + 1) (by positivity)
/-- Mean, raw second moment and covariance operator of a law. -/
def statistics (ν : ProbabilityMeasure E) : E × (ℝ × (E →L[ℝ] E)) :=
  (∫ y, y ∂(ν : Measure E), ∫ y, ‖y‖ ^ 2 ∂(ν : Measure E), Covariance.operator (ν : Measure E))
/-- The two-step laws: Gaussian smoothing `n`, then quadratic tilt with tiltRate `δ_k`. -/
def rowLaw (μ : ProbabilityMeasure E) (n k : ℕ) : ProbabilityMeasure E :=
  Probability.quadraticTiltLaw (gaussianSeq μ n) (tiltRate k) (tiltRate_pos k).le
/-- The law of the produced regular potential at smoothing `n+1` and tilt tiltRate `δ_k`. -/
def regularSeq {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (n k : ℕ) : ProbabilityMeasure E :=
  (regularPotential_quadraticPotential hρ
    (by positivity : (0 : ℝ) < (n : ℝ) + 1) (tiltRate_pos k)).law
end GaussianSmoothing
end LogConcave
end KLS
end FunctionalInequalities
end


