-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:21:18.370365+00:00
-- url     : https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8
-- title:
--   Import context: KLS/LogConcave/Density/GaussianSmoothing/Moments
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`, `FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives`, `FunctionalInequalities.Probability.Product`, `FunctionalInequalities.Probability.Covariance.Basic`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, and `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments`. It also directly imports the external prerequisite module `Mathlib.MeasureTheory.Group.IntegralConvolution`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
--   import FunctionalInequalities.Probability.Product
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import Mathlib.MeasureTheory.Group.IntegralConvolution
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`Analysis/BakryEmery/Tilt/LocalDerivatives`](https://prove2.me/theorems/62e3d2e2-1b96-4afe-b27b-faf9f7826a95), [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5), [`KLS/LogConcave/Density/BorellRepresentation/Moments`](https://prove2.me/theorems/e5df2dc6-6ebd-4244-bfb5-41d46b1c70d1).
--
--   Theorems in source order:
--
--   - [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e)
--   - [`gaussianLaw_laplace`](https://prove2.me/theorems/1f27ed11-f52e-4f6b-b3d6-50fd828fde34)
--   - [`gaussianLaw_mean_zero`](https://prove2.me/theorems/7a2e1852-6769-4381-9c3b-30c6200fe337)
--   - [`gaussianLaw_inner_sq`](https://prove2.me/theorems/a1a65a5b-0fa7-48a4-bd6f-576a0f2e068e)
--   - [`smoothedLaw_mean`](https://prove2.me/theorems/594d731d-a219-4d57-a38e-26c06cf13154)
--   - [`gaussianLaw_variance`](https://prove2.me/theorems/d32b8812-f3da-46ba-8045-625ae0264890)
--   - [`smoothedLaw_variance`](https://prove2.me/theorems/10f92691-c2f0-485d-97ef-571ea1b1d2c5)
--   - [`smoothedLaw_covarianceBilin`](https://prove2.me/theorems/c357a868-1434-4039-b92d-a0210d64482e)
--   - [`smoothedLaw_inner_sq`](https://prove2.me/theorems/e994f4a0-91dd-45b0-a526-8baeb50d6e6b)
--   - [`smoothedLaw_norm_sq`](https://prove2.me/theorems/8855ba81-dd57-4aab-98f3-9959c375040d)
--   - [`gaussianLaw_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/123bb3a0-2332-4e67-a78a-7bf12553f53a)
--   - [`gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/c0deab00-4b66-4ff2-9322-12a13e5f7645)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L1-L569 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments


