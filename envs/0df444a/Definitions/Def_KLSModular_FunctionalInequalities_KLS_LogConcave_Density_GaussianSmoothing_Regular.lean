-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:53:27.711024+00:00
-- url     : https://prove2.me/theorems/d0116214-37fa-4895-a2c9-05d0dd946cde
-- title:
--   Regular potential from Gaussian smoothing and quadratic tilting
-- statement:
--   `quadraticPotential ρ s δ` is the function $V_s(x)+\delta\|x\|^2/2$, where $V_s$ is the negative logarithm of the normalized Gaussian-smoothed density. If $s>0$ and $\delta>0$, `regularPotential_quadraticPotential` proves that this is a `RegularPotential` with lower Hessian bound $\delta$ and upper Hessian bound $2s+\delta$. The result also includes the temperate-growth and convexity premises needed by the regular-potential structure.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Growth
--   import FunctionalInequalities.KLS.LogConcave.Regular.Basic
--   import FunctionalInequalities.Probability.QuadraticTilt
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def quadraticPotential (ρ : E → ℝ) (s δ : ℝ) : E → ℝ :=
--     fun y => potential ρ s y + δ / 2 * ‖y‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/Growth`](https://prove2.me/theorems/15bbe10d-a5f5-491d-b1b9-01f1612573e1), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Probability/QuadraticTilt`](https://prove2.me/theorems/60d2b9ef-6970-4c75-8c09-768a09afafb4).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Regular.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Regular` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Regular.lean#L44-L56 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Regular`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Growth
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticTilt

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The potential `V_s + δ/2‖·‖²` of the Gaussian smoothing followed by the quadratic tilt (BKL (12)). -/
noncomputable def quadraticPotential (ρ : E → ℝ) (s δ : ℝ) : E → ℝ :=
  fun y => potential ρ s y + δ / 2 * ‖y‖ ^ 2
/-- **The regular approximation produces a regular potential** (BKL Section 2, p. 5): for a probability
law with a Borell density, `s > 0`, `δ > 0`, the potential `V_s + δ/2‖·‖²` is regular with curvature
bounds `δ ≤ ∇² ≤ 2s + δ` (`ε = 1/(2s)`). -/
theorem regularPotential_quadraticPotential {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : IsBorellDensity μ volume ρ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    RegularPotential (quadraticPotential ρ s δ) δ (2 * s + δ) := by
  exact RegularPotential.of_convexOn_hasTemperateGrowth
    (potential_hasTemperateGrowth hρ hs)
    (potential_convex hρ hs) hδ (bilinearIteratedFDerivTwo_potential_le hρ hs)
end GaussianSmoothing
end LogConcave
end KLS
end FunctionalInequalities


