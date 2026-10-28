-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient
-- name    : KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:15:19.521987+00:00
-- url     : https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467
-- title:
--   Import context: Energy/Euclidean/ZeroGradient
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Energy.Euclidean.ZeroGradient` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.Energy.Euclidean.WeakDerivative`. It also directly imports the external prerequisite module `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Euclidean.WeakDerivative
--   import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Euclidean/WeakDerivative`](https://prove2.me/theorems/c4b37c13-923e-4442-bcbf-73e18432fd7e).
--
--   Theorems in source order:
--
--   - [`norm_mul_fderiv_comp_sub_smul_le`](https://prove2.me/theorems/ac853596-8eb4-4516-8eb3-374b5c046e01)
--   - [`hasDerivAt_integral_mul_translate`](https://prove2.me/theorems/578ccf2b-12bc-48b1-889e-1bee05d7af56)
--   - [`integral_mul_sub_translate_eq_zero`](https://prove2.me/theorems/92d2bdd3-6571-4798-95e4-ba80de2514d6)
--   - [`locallyIntegrable_comp_add_right`](https://prove2.me/theorems/20004fc3-1194-490c-af8c-f5c2147ffe0b)
--   - [`ae_add_eq_of_integral_mul_fderiv_eq_zero`](https://prove2.me/theorems/41fc0968-9c28-44e9-bc3c-b52d1929e169)
--   - [`exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`](https://prove2.me/theorems/582959f3-9760-49aa-8308-fec3d495a4ec)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean) · `FunctionalInequalities.Energy.Euclidean.ZeroGradient` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L1-L392 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, import-context bundle `KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff


