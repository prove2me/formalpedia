-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:51:55.288551+00:00
-- url     : https://prove2.me/theorems/43fb64bd-b52a-486a-aa88-c80fa40c379d
-- title:
--   Import context: Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Cutoff.Profile`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic`, and `FunctionalInequalities.Analysis.Convex.Coercivity`. It also directly imports the external prerequisite modules `Mathlib.LinearAlgebra.Matrix.PosDef` and `Mathlib.Topology.Instances.Matrix`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Cutoff.Profile
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
--   import FunctionalInequalities.Analysis.Convex.Coercivity
--   import Mathlib.LinearAlgebra.Matrix.PosDef
--   import Mathlib.Topology.Instances.Matrix
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Basic`](https://prove2.me/theorems/b8e832e5-3953-4fab-bf6b-4ce0c2f4bdfe), [`Analysis/Convex/Coercivity`](https://prove2.me/theorems/2ca7e523-4058-4fe5-bce8-76262b1a4a2d).
--
--   Theorems in source order:
--
--   - [`integral_profile_inverse_energy_eq_drift`](https://prove2.me/theorems/37eca32c-ff0d-4e58-b29e-ac1ed53cd43e)
--   - [`ae_hessianMatrix_comp_profile`](https://prove2.me/theorems/a20a6531-08f1-4bad-8e32-e9848449abfb)
--   - [`exists_C1_height_generator_defect_bound`](https://prove2.me/theorems/e4f716ac-97c9-41de-a9ed-1a6f2468efbb)
--   - [`exists_scaled_weak_inverse_hessian_cutoffs`](https://prove2.me/theorems/668b9b15-6105-43f9-a200-099e2fd7f3b7)
--   - [`integral_rough_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/f2c8c826-3a52-44a7-a05b-5384299f9b32)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean) · `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L1-L1011 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Coercivity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix


