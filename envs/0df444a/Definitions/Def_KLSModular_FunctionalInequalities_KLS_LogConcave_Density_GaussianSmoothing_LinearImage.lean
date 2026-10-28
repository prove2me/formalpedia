-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:00:08.189729+00:00
-- url     : https://prove2.me/theorems/65252c7c-8be3-4f9a-a8e7-be00ac3deb3b
-- title:
--   Import context: KLS/LogConcave/Density/GaussianSmoothing/LinearImage
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`, `FunctionalInequalities.KLS.LogConcave.Isotropic`, `FunctionalInequalities.Probability.LogConcave`, `FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity`, `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic`, `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction`, `FunctionalInequalities.Probability.AffineSupport`, and `FunctionalInequalities.Probability.Transport`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
--   import FunctionalInequalities.KLS.LogConcave.Isotropic
--   import FunctionalInequalities.Probability.LogConcave
--   import FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction
--   import FunctionalInequalities.Probability.AffineSupport
--   import FunctionalInequalities.Probability.Transport
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`KLS/LogConcave/Isotropic`](https://prove2.me/theorems/35471368-b77f-4600-8554-699e6845e252), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/LogConcave/Density/AbsoluteContinuity`](https://prove2.me/theorems/e38f29f9-7558-463f-abf1-1d63f7b51b32), [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548), [`KLS/LogConcave/Density/BorellRepresentation/Construction`](https://prove2.me/theorems/533a10b6-a945-4efc-bb81-9cda52d67d80), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Theorems in source order:
--
--   - [`gaussian_product_latent_map`](https://prove2.me/theorems/3d05d9ff-f20e-4259-8e76-31eb720af291)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/LinearImage.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/LinearImage.lean#L1-L71 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport


