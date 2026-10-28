-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:12:51.837455+00:00
-- url     : https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1
-- title:
--   Import context: KLS/BKL/Localization/CovarianceGenerator
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.Coefficients`, `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, `FunctionalInequalities.Probability.Posterior.LogPartition`, `FunctionalInequalities.Analysis.BakryEmery.Calculus`, `FunctionalInequalities.KLS.BKL.Posterior.Covariance`, and `FunctionalInequalities.Probability.Diffusion.Generator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Coefficients
--   import FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator
--   import FunctionalInequalities.Probability.Posterior.LogPartition
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`generator_posteriorExpectation`](https://prove2.me/theorems/e97e7cc4-ef35-4351-ba82-cfe8145edbfe)
--   - [`generator_inner_cov`](https://prove2.me/theorems/e39e89cd-78e0-4dd6-b485-29a06311ff5b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean) · `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean#L1-L206 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator


