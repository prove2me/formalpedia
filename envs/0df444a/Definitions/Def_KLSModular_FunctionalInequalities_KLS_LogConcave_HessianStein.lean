-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:51:16.248991+00:00
-- url     : https://prove2.me/theorems/72cb6534-e95d-45a6-ad0a-93acef4b771e
-- title:
--   Import context: KLS/LogConcave/HessianStein
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.HessianStein` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Operator.Coordinates`, `FunctionalInequalities.Probability.Stein.Kernel`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, `FunctionalInequalities.Probability.Stein.HessianKernel`, `FunctionalInequalities.KLS.Isotropic`, `FunctionalInequalities.KLS.LogConcave.Stein`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, and `FunctionalInequalities.Analysis.BakryEmery.Calculus`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   import FunctionalInequalities.Probability.Stein.Kernel
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Probability.Stein.HessianKernel
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.KLS.LogConcave.Stein
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Probability/Stein/HessianKernel`](https://prove2.me/theorems/ca510456-989b-410d-a253-55ac463b3962), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/Stein`](https://prove2.me/theorems/22b48506-76c6-49df-a6bc-29520a2137c3), [`Analysis/BakryEmery/IntegrationByParts/LipschitzHessian`](https://prove2.me/theorems/a33bc411-81aa-4352-b34a-c6253ee0ed0a), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a).
--
--   Theorems in source order:
--
--   - [`source_stein_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/abe8f632-2fbe-4518-9208-6c81be572011)
--   - [`source_affine_stein_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/e5b3ff9c-092e-463b-98ea-ed142c530c1b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean) · `FunctionalInequalities.KLS.LogConcave.HessianStein` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean#L1-L445 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.HessianStein`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Stein
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus


