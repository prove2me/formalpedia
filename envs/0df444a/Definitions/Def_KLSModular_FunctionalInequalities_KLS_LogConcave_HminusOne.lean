-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:01:19.703124+00:00
-- url     : https://prove2.me/theorems/4dc71c7a-51b5-45a0-8de3-41cf287dbc05
-- title:
--   Import context: KLS/LogConcave/HminusOne
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.HminusOne` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range`, `FunctionalInequalities.Analysis.BakryEmery.Curvature`, `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, and `FunctionalInequalities.KLS.LogConcave.BrascampLieb`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range
--   import FunctionalInequalities.Analysis.BakryEmery.Curvature
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
--   import FunctionalInequalities.KLS.LogConcave.BrascampLieb
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/Range`](https://prove2.me/theorems/a24adaa9-3bf7-4b4a-8f86-f94e3c7a1ac4), [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461), [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`KLS/LogConcave/BrascampLieb`](https://prove2.me/theorems/ef0b3d78-2213-4c3c-ab7c-7dd44bfe1cfb).
--
--   Theorems in source order:
--
--   - [`nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq`](https://prove2.me/theorems/b98a51cc-c659-42c7-9c41-59b73de13a36)
--   - [`sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq`](https://prove2.me/theorems/34cc3097-b38d-4f33-9bd3-39c1af8e4e9d)
--   - [`variance_le_sum_of_partial_dual_bounds`](https://prove2.me/theorems/87d34084-ab4b-4b3e-96bf-c24d3921e663)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean) · `FunctionalInequalities.KLS.LogConcave.HminusOne` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L1-L635 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.HminusOne`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb


