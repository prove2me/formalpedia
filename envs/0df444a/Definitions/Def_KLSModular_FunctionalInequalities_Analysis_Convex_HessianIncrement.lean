-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:08:35.185991+00:00
-- url     : https://prove2.me/theorems/ed30c0a7-e1f1-47c8-bf1b-4711117fdb53
-- title:
--   Import context: Analysis/Convex/HessianIncrement
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Convex.HessianIncrement` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Cutoff.Translation`, `FunctionalInequalities.Analysis.Convex.SecondDifference`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, and `FunctionalInequalities.Analysis.Convex.Viscosity`. It also directly imports the external prerequisite module `Mathlib.MeasureTheory.Function.LocallyIntegrable`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Cutoff.Translation
--   import FunctionalInequalities.Analysis.Convex.SecondDifference
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
--   import FunctionalInequalities.Analysis.Convex.Viscosity
--   import Mathlib.MeasureTheory.Function.LocallyIntegrable
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Cutoff/Translation`](https://prove2.me/theorems/7e49ee02-1556-4ccf-9755-78f397c2f933), [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8), [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Theorems in source order:
--
--   - [`integrable_hessian_increment_energy`](https://prove2.me/theorems/629a963f-e2b8-40f9-bcc4-6dab330a953b)
--   - [`integral_mul_hessian_increment_le`](https://prove2.me/theorems/ed5fdd74-9c13-4186-ad4f-40dd1e40ed9c)
--   - [`exists_hessian_cutoff_sq_difference_bound`](https://prove2.me/theorems/54515687-f5b2-40e0-b262-9c29f518ff9c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean) · `FunctionalInequalities.Analysis.Convex.HessianIncrement` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L1-L459 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Convex.HessianIncrement`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Translation
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Mathlib.MeasureTheory.Function.LocallyIntegrable


