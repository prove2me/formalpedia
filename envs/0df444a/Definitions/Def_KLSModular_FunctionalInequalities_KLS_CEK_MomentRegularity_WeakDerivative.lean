-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakDerivative
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:14:57.014659+00:00
-- url     : https://prove2.me/theorems/7f428f36-c3e2-46b9-8fdd-19a83012aba0
-- title:
--   Import context: KLS/CEK/MomentRegularity/WeakDerivative
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, `FunctionalInequalities.Analysis.Convex.Coercivity`, `FunctionalInequalities.Analysis.Convex.GradientLipschitz`, `FunctionalInequalities.Analysis.Convex.HessianRegularity`, `FunctionalInequalities.Analysis.Lipschitz.Exponential`, `FunctionalInequalities.Analysis.Lipschitz.Gradient`, `FunctionalInequalities.Analysis.Matrix.DeterminantDerivative`, `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.KLS.Isotropic`, and `FunctionalInequalities.KLS.CEK.MomentRegularity.Potential`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.Convex.Coercivity
--   import FunctionalInequalities.Analysis.Convex.GradientLipschitz
--   import FunctionalInequalities.Analysis.Convex.HessianRegularity
--   import FunctionalInequalities.Analysis.Lipschitz.Exponential
--   import FunctionalInequalities.Analysis.Lipschitz.Gradient
--   import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
--   import FunctionalInequalities.Analysis.Matrix.WeakDerivative
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.KLS.CEK.MomentRegularity.Potential
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/Convex/Coercivity`](https://prove2.me/theorems/2ca7e523-4058-4fe5-bce8-76262b1a4a2d), [`Analysis/Convex/GradientLipschitz`](https://prove2.me/theorems/b5069800-f62d-405b-8e8b-6b9408cea016), [`Analysis/Convex/HessianRegularity`](https://prove2.me/theorems/3de085c3-1487-424e-b91c-badb9e79b607), [`Analysis/Lipschitz/Exponential`](https://prove2.me/theorems/821fcb62-3c82-4d91-bc63-d727b7d1cab1), [`Analysis/Lipschitz/Gradient`](https://prove2.me/theorems/c121ae0a-019e-498c-bab1-b5d194574dc8), [`Analysis/Matrix/DeterminantDerivative`](https://prove2.me/theorems/46a9a92e-982e-4a04-af01-9373c2e17873), [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/CEK/MomentRegularity/Potential`](https://prove2.me/theorems/76e138af-1ba7-464e-acf1-d307e8ead30a).
--
--   Theorems in source order:
--
--   - [`exists_regular_moment_weak_tensor`](https://prove2.me/theorems/795e959e-8359-45c4-b731-4112d0057128)
--   - [`exists_regular_moment_weak_first_derivative`](https://prove2.me/theorems/db7072c4-5f0c-4a46-9f63-f4f194d792ed)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean) · `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean#L1-L291 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakDerivative`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Coercivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_GradientLipschitz
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Lipschitz_Exponential
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Potential


