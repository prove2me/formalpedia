-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature
-- name    : KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:22:59.262268+00:00
-- url     : https://prove2.me/theorems/2d0d4681-a28b-4386-bf7f-208cba5fd2c8
-- title:
--   Import context: Analysis/Semigroup/Generated/Curvature
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Semigroup.Generated.FormDomain`, `FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative`, and `FunctionalInequalities.Analysis.Semigroup.VonNeumann`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Calculus.Deriv.MeanValue` and `Mathlib.Analysis.SpecialFunctions.ExpDeriv`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Semigroup.Generated.FormDomain
--   import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
--   import FunctionalInequalities.Analysis.Semigroup.VonNeumann
--   import Mathlib.Analysis.Calculus.Deriv.MeanValue
--   import Mathlib.Analysis.SpecialFunctions.ExpDeriv
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Semigroup/Generated/FormDomain`](https://prove2.me/theorems/1bad6be8-1b71-47ad-839b-2965f4bb0242), [`Analysis/Semigroup/Generated/TimeDerivative`](https://prove2.me/theorems/b3d8e0b7-8cea-4a59-87d9-a8d37efcca52), [`Analysis/Semigroup/VonNeumann`](https://prove2.me/theorems/de8bc764-27c8-4eea-80bc-26a005cde179).
--
--   Theorems in source order:
--
--   - [`norm_map_apply_sq_eq_inner`](https://prove2.me/theorems/c2084695-8d99-499c-9d32-ea5e8a16d7be)
--   - [`hasDerivAt_inner_apply`](https://prove2.me/theorems/f5643287-fcd8-4cb8-adec-bac864e18749)
--   - [`le_exp_mul_of_hasDerivAt_le`](https://prove2.me/theorems/38febeed-57be-4f77-b86b-1ca1d79ba62c)
--   - [`norm_map_apply_sq_le_exp_of_mem_adjointComp`](https://prove2.me/theorems/3e1e0324-94fa-4fd6-b2c3-3d7551ff2d12)
--   - [`norm_map_apply_sq_le_exp`](https://prove2.me/theorems/8f943860-f6e7-4593-a4f7-2a7ee8a97f10)
--   - [`norm_sq_sub_norm_apply_sq_le`](https://prove2.me/theorems/d85e3676-603e-4937-ac22-4f0ac1d2765d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean) · `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L1-L586 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Curvature`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_TimeDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


