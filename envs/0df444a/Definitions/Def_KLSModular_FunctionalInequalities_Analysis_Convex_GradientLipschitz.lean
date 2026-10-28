-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_GradientLipschitz
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_GradientLipschitz
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:06:56.522703+00:00
-- url     : https://prove2.me/theorems/b5069800-f62d-405b-8e8b-6b9408cea016
-- title:
--   Import context: Analysis/Convex/GradientLipschitz
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Convex.GradientLipschitz` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Convex.Viscosity`, `FunctionalInequalities.Analysis.Convex.Alexandrov`, `FunctionalInequalities.Analysis.Convex.Coercivity`, and `FunctionalInequalities.Analysis.Convex.SecondDifference`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Viscosity
--   import FunctionalInequalities.Analysis.Convex.Alexandrov
--   import FunctionalInequalities.Analysis.Convex.Coercivity
--   import FunctionalInequalities.Analysis.Convex.SecondDifference
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b), [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905), [`Analysis/Convex/Coercivity`](https://prove2.me/theorems/2ca7e523-4058-4fe5-bce8-76262b1a4a2d), [`Analysis/Convex/SecondDifference`](https://prove2.me/theorems/5412cb80-13f4-48d5-ab21-d4aec90af26d).
--
--   Theorems in source order:
--
--   - [`secondDifference_le_of_map_gradient`](https://prove2.me/theorems/8a48698f-79ec-4b96-966b-75b5ba3d4373)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean) · `FunctionalInequalities.Analysis.Convex.GradientLipschitz` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean#L1-L199 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Convex.GradientLipschitz`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Convex_GradientLipschitz`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Coercivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference


