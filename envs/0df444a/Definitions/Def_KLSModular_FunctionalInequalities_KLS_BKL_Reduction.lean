-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Reduction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:25:39.002656+00:00
-- url     : https://prove2.me/theorems/777aa78c-b385-4e2a-916c-1b5126410eae
-- title:
--   Import context: KLS/BKL/Reduction
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Reduction` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.TaylorBound`, `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion`, `FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives`, and `FunctionalInequalities.KLS.LogConcave.IsotropicReduction`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.TaylorBound
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
--   import FunctionalInequalities.KLS.LogConcave.IsotropicReduction
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/TaylorBound`](https://prove2.me/theorems/ef8651c6-ddf2-4f86-883a-e9e4c00f2d13), [`KLS/BKL/PoissonIterate/Criterion`](https://prove2.me/theorems/b6210dc1-894e-490a-a262-24735151f6b5), [`Analysis/BakryEmery/Tilt/LocalDerivatives`](https://prove2.me/theorems/62e3d2e2-1b96-4afe-b27b-faf9f7826a95), [`KLS/LogConcave/IsotropicReduction`](https://prove2.me/theorems/71545edb-cd76-4fa7-a5a9-f3cfaa7db601).
--
--   Theorems in source order:
--
--   - [`coordTensor_taylorTensor_one_apply`](https://prove2.me/theorems/a9935a3a-2011-4a81-95f1-d32208e68e3c)
--   - [`Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries`](https://prove2.me/theorems/368cfad9-ddaa-46ae-9c1e-acc8bb0d753f)
--   - [`poincare_le_of_cumulantBound`](https://prove2.me/theorems/0b4bd144-4221-4e5f-a91d-90cbadac41af)
--   - [`localSlope_le_of_cumulantBound_all`](https://prove2.me/theorems/cb774c5b-d478-4527-a81e-37c436cdedf4)
--   - [`conjecture_of_cumulantBound`](https://prove2.me/theorems/844c5956-2149-46f9-8369-bc8853a7bf38)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean) · `FunctionalInequalities.KLS.BKL.Reduction` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L1-L351 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Reduction`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Reduction`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction


