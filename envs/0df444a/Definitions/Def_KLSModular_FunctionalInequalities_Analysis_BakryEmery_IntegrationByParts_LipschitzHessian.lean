-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:24:19.825283+00:00
-- url     : https://prove2.me/theorems/a33bc411-81aa-4352-b34a-c6253ee0ed0a
-- title:
--   Import context: Analysis/BakryEmery/IntegrationByParts/LipschitzHessian
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.ConvexHessian`, `FunctionalInequalities.Analysis.Cutoff.SmoothBall`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, and `FunctionalInequalities.Analysis.WeakDerivative.Calculus`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.ConvexHessian
--   import FunctionalInequalities.Analysis.Cutoff.SmoothBall
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/IntegrationByParts/ConvexHessian`](https://prove2.me/theorems/9e175e47-8f9e-4f9e-bc34-a0a0891d0139), [`Analysis/Cutoff/SmoothBall`](https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Theorems in source order:
--
--   - [`integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul`](https://prove2.me/theorems/6627935a-8ab5-4069-9ba3-e8134c1348f4)
--   - [`integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`](https://prove2.me/theorems/80255608-689e-4cd7-80cc-3b2a722fd329)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean) · `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L1-L325 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_ConvexHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus


