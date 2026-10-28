-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:41:16.43551+00:00
-- url     : https://prove2.me/theorems/fc1e6296-7365-450f-8b02-bedf52fdeb49
-- title:
--   Import context: KLS/BKL/Localization/CutoffEnergy/Boundary
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator`, `FunctionalInequalities.KLS.BKL.Localization.Standardization`, `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, `FunctionalInequalities.KLS.BKL.CompactReduction`, `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic`, `FunctionalInequalities.KLS.BKL.Localization.Process.Integral`, and `FunctionalInequalities.Probability.Diffusion.Generator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
--   import FunctionalInequalities.KLS.BKL.Localization.Standardization
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.CompactReduction
--   import FunctionalInequalities.KLS.BKL.CumulantEnvelope
--   import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Integral
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/CovarianceGenerator`](https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1), [`KLS/BKL/Localization/Standardization`](https://prove2.me/theorems/d6ac7b3b-4286-4c25-abe4-12ef241d0c20), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`exists_le_setIntegral_div`](https://prove2.me/theorems/5ce5f2ed-8559-4220-9d87-a84f56353c15)
--   - [`IsEldanCutoff.integral_energy_le_weighted_add`](https://prove2.me/theorems/c81a7719-fcaa-451a-93ca-ddc74bf08eb5)
--   - [`IsEldanCutoff.exists_weighted_energy_le`](https://prove2.me/theorems/0093b479-64bc-4ff4-8d31-2c2c61eec957)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean) · `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean#L1-L370 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Standardization
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator


