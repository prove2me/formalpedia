-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:07:30.997676+00:00
-- url     : https://prove2.me/theorems/032e441a-7b5c-4cf8-9242-29a059b98a48
-- title:
--   Import context: KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling`, `FunctionalInequalities.KLS.LogConcave.HminusOne`, `FunctionalInequalities.Probability.QuadraticVariance`, `FunctionalInequalities.Analysis.BakryEmery.Calculus`, `FunctionalInequalities.Probability.LogConcave`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, `FunctionalInequalities.Probability.AffineSupport`, `FunctionalInequalities.Probability.Moments`, `FunctionalInequalities.Probability.Stein.Kernel`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, and `FunctionalInequalities.Probability.Transport`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling
--   import FunctionalInequalities.KLS.LogConcave.HminusOne
--   import FunctionalInequalities.Probability.QuadraticVariance
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Probability.LogConcave
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
--   import FunctionalInequalities.Probability.AffineSupport
--   import FunctionalInequalities.Probability.Moments
--   import FunctionalInequalities.Probability.Stein.Kernel
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Probability.Transport
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling`](https://prove2.me/theorems/ec60ae0c-90e6-43f3-859c-75d3c6dd9a5f), [`KLS/LogConcave/HminusOne`](https://prove2.me/theorems/4dc71c7a-51b5-45a0-8de3-41cf287dbc05), [`Probability/QuadraticVariance`](https://prove2.me/theorems/8f374ce2-317b-44db-96d6-94eef9130b1f), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`KLS/LogConcave/Density/GaussianSmoothing/LinearImage`](https://prove2.me/theorems/65252c7c-8be3-4f9a-a8e7-be00ac3deb3b), [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Theorems in source order:
--
--   - [`gaussian_smoothed_quadratic_variance_le_latent_energy`](https://prove2.me/theorems/b06bef5a-93db-4e5d-b4b0-013d668182b2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance.lean#L1-L160 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport


