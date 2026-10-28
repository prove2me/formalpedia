-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:59:43.126017+00:00
-- url     : https://prove2.me/theorems/a009d134-31d2-47e2-823a-2b8d35d6fdf8
-- title:
--   Import context: Analysis/Convex/LegendreVariation/Derivative
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment` and `FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Calculus.Gradient.Basic` and `Mathlib.Analysis.Calculus.FDeriv.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment
--   import FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.Analysis.Calculus.FDeriv.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/LegendreVariation/Attainment`](https://prove2.me/theorems/8fff00c5-0262-4f99-9cab-27221baba48b), [`Analysis/Convex/LegendreVariation/Perturbation`](https://prove2.me/theorems/e7c006a8-befd-4287-9bdd-21d766535e08).
--
--   Theorems in source order:
--
--   - [`exists_delta_nearMaximizer_norm_sub_gradient_lt`](https://prove2.me/theorems/72eb7aa6-074f-46cd-aef2-551ce162488e)
--   - [`hasDerivAt_legendre_add_smul_of_dualDifferentiable`](https://prove2.me/theorems/53a6ee6c-57c2-4889-bf33-e52e9986092d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean) · `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L1-L440 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Perturbation
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic


