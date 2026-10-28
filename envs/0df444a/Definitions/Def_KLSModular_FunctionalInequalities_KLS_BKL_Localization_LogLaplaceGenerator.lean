-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:10:14.987206+00:00
-- url     : https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf
-- title:
--   Import context: KLS/BKL/Localization/LogLaplaceGenerator
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.Coefficients`, `FunctionalInequalities.Probability.Posterior.LogPartition`, `FunctionalInequalities.KLS.BKL.Posterior.Covariance`, and `FunctionalInequalities.Probability.Diffusion.Generator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Coefficients
--   import FunctionalInequalities.Probability.Posterior.LogPartition
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/LogPartition`](https://prove2.me/theorems/b716da65-348c-498f-97a9-23cbe395f8fd), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`fderiv_fderiv_fst_dir`](https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789)
--   - [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43)
--   - [`sum_inner_inverseSqrt_sq`](https://prove2.me/theorems/d2123cde-3328-49c8-bb38-74191da51e4b)
--   - [`generator_posteriorExpectation_exp_inner`](https://prove2.me/theorems/6a6bdaa6-0ece-4bfe-854e-2c005a8cead7)
--   - [`posteriorExpectation_exp_inner_eq_exp`](https://prove2.me/theorems/66696a0d-fac3-4245-986c-d8e413dc01d5)
--   - [`fderiv_logLaplace_fst_dir`](https://prove2.me/theorems/0fd2f814-6862-496a-98f2-b2c923618182)
--   - [`generator_logLaplace_posterior`](https://prove2.me/theorems/d04c501c-dd44-4e05-9714-2e8906ff495e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean) · `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L1-L340 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator


