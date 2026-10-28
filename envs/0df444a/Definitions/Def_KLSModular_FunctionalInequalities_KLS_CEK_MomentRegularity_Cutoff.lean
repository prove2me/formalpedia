-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Cutoff
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Cutoff
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:18:55.434594+00:00
-- url     : https://prove2.me/theorems/75cc6def-529a-4f83-991b-244816282c31
-- title:
--   Import context: KLS/CEK/MomentRegularity/Cutoff
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.MomentRegularity.Cutoff` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.KLS.Isotropic`, and `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Basic`](https://prove2.me/theorems/b8e832e5-3953-4fab-bf6b-4ce0c2f4bdfe), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff`](https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/CEK/MomentRegularity/WeakHessian`](https://prove2.me/theorems/31ee248b-daaa-4574-a15c-d87e43ddfa6c).
--
--   Theorems in source order:
--
--   - [`exists_regular_moment_weak_cutoffs`](https://prove2.me/theorems/22593b66-6737-483a-a9c8-aa66569b266d)
--   - [`exists_regular_moment_bounded_weak_cutoff_testing`](https://prove2.me/theorems/6a1cac66-e876-4989-9b29-728e3e2018ac)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Cutoff.lean) · `FunctionalInequalities.KLS.CEK.MomentRegularity.Cutoff` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Cutoff.lean#L1-L432 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.MomentRegularity.Cutoff`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Cutoff`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakHessian


