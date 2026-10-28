-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_PartitionVariation
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_PartitionVariation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:07:46.608012+00:00
-- url     : https://prove2.me/theorems/e725e7ab-6aec-4f2c-8e87-f90cf0f5d355
-- title:
--   Import context: KLS/CEK/PartitionVariation
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.PartitionVariation` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.CEK.BoundedPrimal`, `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative`, and `FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Calculus.ParametricIntegral` and `Mathlib.Analysis.Calculus.Rademacher`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.ParametricIntegral
--   import Mathlib.Analysis.Calculus.Rademacher
--   import FunctionalInequalities.KLS.CEK.BoundedPrimal
--   import FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative
--   import FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/CEK/BoundedPrimal`](https://prove2.me/theorems/9d6c6c4d-d34a-48a4-9377-2f50d4a22e15), [`Analysis/Convex/LegendreVariation/Derivative`](https://prove2.me/theorems/a009d134-31d2-47e2-823a-2b8d35d6fdf8), [`Analysis/Convex/LegendreVariation/Perturbation`](https://prove2.me/theorems/e7c006a8-befd-4287-9bdd-21d766535e08).
--
--   Theorems in source order:
--
--   - [`hasDerivAt_integral_exp_neg_legendre_add_smul`](https://prove2.me/theorems/302acb49-a8f6-47fd-812e-b58a38e4f610)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean) · `FunctionalInequalities.KLS.CEK.PartitionVariation` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean#L1-L243 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.PartitionVariation`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_PartitionVariation`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_BoundedPrimal
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Perturbation


