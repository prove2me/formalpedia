-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:51:54.406756+00:00
-- url     : https://prove2.me/theorems/4d759700-9cad-4791-aded-7197e3d56cfa
-- title:
--   Import context: KLS/LogConcave/WeakBrascampLieb
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.BrascampLieb`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakLaplacian`, `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, and `FunctionalInequalities.Analysis.Matrix.Positivity`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.BrascampLieb
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakLaplacian
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.Matrix.Positivity
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/BrascampLieb`](https://prove2.me/theorems/ef0b3d78-2213-4c3c-ab7c-7dd44bfe1cfb), [`Analysis/BakryEmery/IntegrationByParts/WeakLaplacian`](https://prove2.me/theorems/db3f6cfa-f4e0-461a-859a-e5e7e56c5272), [`Analysis/BakryEmery/Bochner/Lipschitz`](https://prove2.me/theorems/0d3e8510-7673-4d06-9cae-b7b7fef307a8), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Theorems in source order:
--
--   - [`compact_weak_variational_estimate`](https://prove2.me/theorems/a0f061ff-8443-47ab-968d-50cf20a09f59)
--   - [`scalar_brascamp_lieb_weak_finite_energy`](https://prove2.me/theorems/e67ea706-0bd9-4ce6-a4b9-8b19dd948f1a)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean) · `FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean#L1-L175 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakLaplacian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity


