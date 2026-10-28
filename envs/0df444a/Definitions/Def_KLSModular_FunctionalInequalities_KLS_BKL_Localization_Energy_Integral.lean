-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Integral
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Integral
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:38:56.121886+00:00
-- url     : https://prove2.me/theorems/f4a73439-9c30-4a80-a66d-ff72b684af83
-- title:
--   Import context: KLS/BKL/Localization/Energy/Integral
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.Energy.Integral` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.Process.Integral`, `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic`, `FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity`, `FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation`, `FunctionalInequalities.KLS.BKL.Localization.Energy.Bound`, `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, `FunctionalInequalities.Analysis.Tensor.EnergyForm`, `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, and `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Integral
--   import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation
--   import FunctionalInequalities.KLS.BKL.Localization.Energy.Bound
--   import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
--   import FunctionalInequalities.Analysis.Tensor.EnergyForm
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`KLS/BKL/Localization/Energy/Regularity`](https://prove2.me/theorems/a5950f32-4ea5-4584-9d29-8056c7b809f6), [`KLS/BKL/CumulantEnergy/Conjugation`](https://prove2.me/theorems/44ac1865-c5a7-46f3-bb27-cb9b8ec7e3f5), [`KLS/BKL/Localization/Energy/Bound`](https://prove2.me/theorems/4ab05ed1-3d8d-48ff-a6a8-e41faa7f3068), [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8), [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918).
--
--   Theorems in source order:
--
--   - [`energy_integral_le_of_generator_ge`](https://prove2.me/theorems/af9c5a0b-2263-46d2-882d-a46979ba6e41)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Integral.lean) · `FunctionalInequalities.KLS.BKL.Localization.Energy.Integral` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Integral.lean#L1-L387 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Integral`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Integral`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Regularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Conjugation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic


