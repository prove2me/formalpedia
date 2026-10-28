-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Regularity
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Regularity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:05:33.068534+00:00
-- url     : https://prove2.me/theorems/a5950f32-4ea5-4584-9d29-8056c7b809f6
-- title:
--   Import context: KLS/BKL/Localization/Energy/Regularity
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, `FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation`, `FunctionalInequalities.Analysis.Tensor.EnergyForm`, `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, `FunctionalInequalities.KLS.BKL.Posterior.Covariance`, `FunctionalInequalities.KLS.BKL.Posterior.Regularity`, and `FunctionalInequalities.Probability.Diffusion.Generator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation
--   import FunctionalInequalities.Analysis.Tensor.EnergyForm
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.KLS.BKL.Posterior.Regularity
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8), [`KLS/BKL/CumulantEnergy/Conjugation`](https://prove2.me/theorems/44ac1865-c5a7-46f3-bb27-cb9b8ec7e3f5), [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`KLS/BKL/Posterior/Regularity`](https://prove2.me/theorems/d3a1b3f7-aa50-410c-a659-85a6897688cc), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`contDiff_cumulantEnergy_posterior`](https://prove2.me/theorems/0b698a15-4131-4b73-a00b-6eecdff79aa2)
--   - [`continuous_generator_of_contDiff_three`](https://prove2.me/theorems/74acc94a-8282-4bc3-ae22-403b6ce74fcc)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Regularity.lean) · `FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Regularity.lean#L1-L127 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Regularity`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Conjugation
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator


