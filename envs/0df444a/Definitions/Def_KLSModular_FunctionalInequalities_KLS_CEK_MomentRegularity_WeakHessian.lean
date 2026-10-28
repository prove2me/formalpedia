-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakHessian
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakHessian
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:16:32.869913+00:00
-- url     : https://prove2.me/theorems/31ee248b-daaa-4574-a15c-d87e43ddfa6c
-- title:
--   Import context: KLS/CEK/MomentRegularity/WeakHessian
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, `FunctionalInequalities.Analysis.Graph.Area`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, `FunctionalInequalities.KLS.Isotropic`, `FunctionalInequalities.Probability.Stein.HessianKernel`, and `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.Graph.Area
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.Probability.Stein.HessianKernel
--   import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8), [`Analysis/BakryEmery/IntegrationByParts/LipschitzHessian`](https://prove2.me/theorems/a33bc411-81aa-4352-b34a-c6253ee0ed0a), [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/Graph/Area`](https://prove2.me/theorems/4ed953bb-1a9c-42c0-9493-50d9d1993faa), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Probability/Stein/HessianKernel`](https://prove2.me/theorems/ca510456-989b-410d-a253-55ac463b3962), [`KLS/CEK/MomentRegularity/WeakDerivative`](https://prove2.me/theorems/7f428f36-c3e2-46b9-8fdd-19a83012aba0).
--
--   Theorems in source order:
--
--   - [`exists_regular_moment_weak_inverse_mean_hessian`](https://prove2.me/theorems/b64484be-d224-455e-abd1-d269ba17fd36)
--   - [`exists_regular_moment_weak_hessian_evolution`](https://prove2.me/theorems/619ac8de-0688-40ce-8cae-70f9e5b6bb5e)
--   - [`exists_regular_moment_bounded_weak_hessian_testing`](https://prove2.me/theorems/dc4e4140-f06c-4b2c-a4ae-c740aa939d81)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean) · `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean#L1-L842 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakHessian`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Graph_Area
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakDerivative


