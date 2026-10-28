-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:52:02.39969+00:00
-- url     : https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16
-- title:
--   Import context: Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Lipschitz.Gradient`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere`, `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, and `FunctionalInequalities.Analysis.Matrix.Integral`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Lipschitz.Gradient
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
--   import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
--   import FunctionalInequalities.Analysis.Matrix.Integral
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Lipschitz/Gradient`](https://prove2.me/theorems/c121ae0a-019e-498c-bab1-b5d194574dc8), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8), [`Analysis/BakryEmery/MongeAmpere`](https://prove2.me/theorems/2b5c2043-7539-4080-9bb7-264ef25c0839), [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/Matrix/Integral`](https://prove2.me/theorems/09aa8c12-3230-447e-89a1-dc642659f2aa).
--
--   Theorems in source order:
--
--   - [`exists_lipschitzWith_weak_fderiv_comp_gradient`](https://prove2.me/theorems/2b6867a4-8c8c-4420-8df5-b75bc2ce4bd7)
--   - [`hasWeakDerivAlong_mongeAmpere_first_rhs`](https://prove2.me/theorems/55f12f10-6c36-4776-96b3-387313b3b590)
--   - [`localLp_hessian_flux_trace_forcing`](https://prove2.me/theorems/0d14ed2a-5f26-4feb-914f-b0d0e87bf35c)
--   - [`integral_array_pair_balance`](https://prove2.me/theorems/6a56d72a-b125-4b6e-9809-d8d6e98e7bf3)
--   - [`integral_weak_hessian_flux_eq_trace_derivative`](https://prove2.me/theorems/6d0b46f6-29ee-4cf1-8e3f-098cb8c41989)
--   - [`ae_hessian_flux_forcing_minus_drift`](https://prove2.me/theorems/838d3785-b396-43ff-b452-a1eb6e64d796)
--   - [`integral_exp_neg_flux_of_unweighted`](https://prove2.me/theorems/ede33e09-7e75-4497-9ed6-66486b1825c1)
--   - [`integral_exp_neg_hessian_flux_eq_curvature_gram`](https://prove2.me/theorems/6d3ddc0c-45c1-4c79-b3d0-33799314293f)
--   - [`integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test`](https://prove2.me/theorems/6c225a3e-8283-4741-ad77-ae9ad7405baf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean) · `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1-L2100 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral


