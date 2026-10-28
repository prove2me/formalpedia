-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:59:15.478359+00:00
-- url     : https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d
-- title:
--   Cumulant gradient vector
-- statement:
--   For a measure $\mu$ on a finite-dimensional real inner-product space $E$ and a list `hs` of vectors, `cumulantVector μ hs` is the Riesz-represented vector corresponding to the continuous linear functional obtained by fixing the first `hs.length` slots of the cumulant of order `hs.length + 1`. Thus its defining property is that pairing it with a vector $w$ yields the corresponding cumulant with $w$ in the final slot. This is a local gradient-jet construction; no additional identity is asserted by the definition.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
--   import FunctionalInequalities.Analysis.Tensor.BasisChange
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import FunctionalInequalities.Probability.Covariance.Positivity
--   import Mathlib.Probability.Moments.IntegrableExpMul
--   import Mathlib.MeasureTheory.Measure.Support
--   import Mathlib.Analysis.InnerProductSpace.Dual
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import FunctionalInequalities.Analysis.IteratedDerivative.GradientJet
--   import FunctionalInequalities.Analysis.IteratedDerivative.Symmetry
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def cumulantVector (μ : Measure E) (hs : List E) : E :=
--     (InnerProductSpace.toDual ℝ E).symm
--       ((cumulant μ (hs.length + 1)).curryRight (fun i => hs.get i))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Analysis/BakryEmery/Tilt/LocalDerivatives`](https://prove2.me/theorems/62e3d2e2-1b96-4afe-b27b-faf9f7826a95), [`Analysis/Tensor/BasisChange`](https://prove2.me/theorems/89846a1e-d28c-484e-94fe-f976ef7e2382), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/Covariance/Positivity`](https://prove2.me/theorems/11f9423c-d823-4cf1-ba54-703b7213bca5), [`Analysis/IteratedDerivative/GradientJet`](https://prove2.me/theorems/2f9ce587-2ee9-4125-9ef5-333d09ad8523), [`Analysis/IteratedDerivative/Symmetry`](https://prove2.me/theorems/c3281ab2-65ad-4ae5-995a-70d685aba1dc).
--
--   Theorems in source order:
--
--   - [`inner_exp_weights`](https://prove2.me/theorems/4f978fb4-52f2-4f2b-90f6-26d81c887136)
--   - [`cumulant_three_eq_integral_of_integrable_exp`](https://prove2.me/theorems/2207a4d5-d176-43bd-8980-82729562a6ee)
--   - [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818)
--   - [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp`](https://prove2.me/theorems/2ebfc9d7-c5cf-4a67-b311-d32be10eee98)
--   - [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis`](https://prove2.me/theorems/d843d70e-8af8-4774-b08a-b195f310d902)
--   - [`cumulant_two_eq_centered_moment_of_integrable_exp`](https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb)
--   - [`iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact`](https://prove2.me/theorems/c850afc5-a923-4019-b001-39ff0f56dd9b)
--   - [`inner_cumulantVector_single_ringInverse_cumulantVector`](https://prove2.me/theorems/9237a40c-7f1f-4233-8865-0d20c1925f94)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean) · `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L517-L521 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_BasisChange
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Gradient.Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_GradientJet
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section GradientJets
/-- The Riesz vector of the last slot of the scalar cumulant of order `hs.length + 1`, the first slots being the
list `hs` (inherited order): `⟪cumulantVector μ hs, w⟫ = κ_{|hs|+1}(hs, w)`. -/
noncomputable def cumulantVector (μ : Measure E) (hs : List E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    ((cumulant μ (hs.length + 1)).curryRight (fun i => hs.get i))
end GradientJets
end BakryEmery
end Analysis
end FunctionalInequalities


