-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:49:31.17139+00:00
-- url     : https://prove2.me/theorems/0d3e8510-7673-4d06-9cae-b7b7fef307a8
-- title:
--   Import context: Analysis/BakryEmery/Bochner/Lipschitz
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Mollification.Hessian`, `FunctionalInequalities.Analysis.BakryEmery.Curvature`, `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, and `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Mollification.Hessian
--   import FunctionalInequalities.Analysis.BakryEmery.Curvature
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Mollification/Hessian`](https://prove2.me/theorems/3226f506-ca93-41c2-b914-cd900f4c6a41), [`Analysis/BakryEmery/Curvature`](https://prove2.me/theorems/cc52420a-ef45-46de-bbc8-eaff81f0f461), [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Theorems in source order:
--
--   - [`integral_weightedLaplacian_sq_eq_of_lipschitz_gradient`](https://prove2.me/theorems/866e6109-1efa-4b77-8325-9da4c4d16ab4)
--   - [`compact_ordinary_diffusion_coercivity_of_lipschitz_gradient`](https://prove2.me/theorems/2333fc8d-b8d0-4b91-abd1-9ba2b3b18409)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean) · `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean#L1-L347 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Hessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator


