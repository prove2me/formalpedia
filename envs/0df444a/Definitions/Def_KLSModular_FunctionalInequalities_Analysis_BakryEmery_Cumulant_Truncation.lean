-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:06:06.461392+00:00
-- url     : https://prove2.me/theorems/1997edb8-3ab3-4dc8-9655-6994bac1ddde
-- title:
--   Import context: Analysis/BakryEmery/Cumulant/Truncation
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic` and `FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives`. It also directly imports the external prerequisite module `Mathlib.Probability.ConditionalProbability`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
--   import Mathlib.Probability.ConditionalProbability
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Analysis/BakryEmery/Tilt/LocalDerivatives`](https://prove2.me/theorems/62e3d2e2-1b96-4afe-b27b-faf9f7826a95).
--
--   Theorems in source order:
--
--   - [`norm_iteratedFDeriv_laplace_cond_sub_le`](https://prove2.me/theorems/b4caad6e-5213-4b24-9630-2723c2fbca35)
--   - [`tendsto_iteratedFDeriv_laplace_cond_closedBall`](https://prove2.me/theorems/57a5ae82-e2eb-414c-9f9c-2995a3f53149)
--   - [`cumulant_eq_taylorComp_cond`](https://prove2.me/theorems/e57746d5-e68b-403d-82bc-29f420d708e4)
--   - [`tendsto_cumulant_cond_closedBall`](https://prove2.me/theorems/5a26c5c6-06d4-47bc-a7e9-de2a1a85735b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean) · `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L1-L253 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Mathlib.Probability.ConditionalProbability


