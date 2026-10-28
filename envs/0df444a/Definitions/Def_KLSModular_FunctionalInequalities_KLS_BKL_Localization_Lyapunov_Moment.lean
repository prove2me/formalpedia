-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:40:12.427238+00:00
-- url     : https://prove2.me/theorems/efd9f37b-5ca3-4919-b8ed-5afbf25b7a3c
-- title:
--   Import context: KLS/BKL/Localization/Lyapunov/Moment
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic`, `FunctionalInequalities.Analysis.Gronwall`, `FunctionalInequalities.KLS.BKL.Localization.Process.Integral`, and `FunctionalInequalities.Probability.Diffusion.Generator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
--   import FunctionalInequalities.Analysis.Gronwall
--   import FunctionalInequalities.KLS.BKL.Localization.Process.Integral
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7), [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`Analysis/Gronwall`](https://prove2.me/theorems/cd710807-c023-4a0e-9183-faaa7308f99a), [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`IsEldanCutoff.integral_lyapunov_le`](https://prove2.me/theorems/d9f68ec0-3a26-4968-8fa3-4c402bb735c1)
--   - [`IsEldanCutoff.measure_norm_gt_le`](https://prove2.me/theorems/132ae609-cd45-4dbe-ab0d-e0f6ebb6fda6)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean) · `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean#L1-L361 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Gronwall
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator


