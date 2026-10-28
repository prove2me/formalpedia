-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:50:20.889297+00:00
-- url     : https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b
-- title:
--   Import context: Analysis/Convex/LegendreVariation/Attainment
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Extremum`, `FunctionalInequalities.Analysis.Convex.AffineMaximum`, and `FunctionalInequalities.Analysis.Convex.Legendre`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Calculus.LocalExtr.Basic`, `Mathlib.Analysis.InnerProductSpace.Calculus`, and `Mathlib.Analysis.Calculus.Gradient.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Extremum
--   import FunctionalInequalities.Analysis.Convex.AffineMaximum
--   import FunctionalInequalities.Analysis.Convex.Legendre
--   import Mathlib.Analysis.Calculus.LocalExtr.Basic
--   import Mathlib.Analysis.InnerProductSpace.Calculus
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Extremum`](https://prove2.me/theorems/e7a84d99-b4b9-489a-a9b9-2b3440d6f223), [`Analysis/Convex/AffineMaximum`](https://prove2.me/theorems/6ce50813-8eec-46a5-abb0-e806e1385307), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Theorems in source order:
--
--   - [`conjugate_maximizer_eq_gradient`](https://prove2.me/theorems/80335e95-bd3b-41ae-b542-89eb54c17879)
--   - [`exists_coercive_tilt_of_mem_interior_legendre_domain`](https://prove2.me/theorems/2a6ee0ab-9933-4999-9219-7fdf5606d335)
--   - [`tiltedObjective_data`](https://prove2.me/theorems/e3e2f5b2-8368-425f-a963-03a46f5caf8c)
--   - [`exists_legendre_maximizer_with_gradient_identity`](https://prove2.me/theorems/0a4c46db-2543-480e-9c88-e7e91f832b89)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean) · `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L1-L374 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Extremum
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic


