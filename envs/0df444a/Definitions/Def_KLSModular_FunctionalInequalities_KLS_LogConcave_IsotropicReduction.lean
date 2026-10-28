-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:58:49.828994+00:00
-- url     : https://prove2.me/theorems/71545edb-cd76-4fa7-a5a9-f3cfaa7db601
-- title:
--   Import context: KLS/LogConcave/IsotropicReduction
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.IsotropicReduction` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation`, `FunctionalInequalities.KLS.LogConcave.Regular.Isometry`, `FunctionalInequalities.KLS.LogConcave.Regular.Poincare`, `FunctionalInequalities.KLS.LogConcave.WeakLimit`, `FunctionalInequalities.KLS.IsotropicSupport`, and `FunctionalInequalities.Poincare.SmoothTest.Comparison`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
--   import FunctionalInequalities.KLS.LogConcave.Regular.Isometry
--   import FunctionalInequalities.KLS.LogConcave.Regular.Poincare
--   import FunctionalInequalities.KLS.LogConcave.WeakLimit
--   import FunctionalInequalities.KLS.IsotropicSupport
--   import FunctionalInequalities.Poincare.SmoothTest.Comparison
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation`](https://prove2.me/theorems/eabcdc52-c914-4c59-b1af-3d43455f910d), [`KLS/LogConcave/Regular/Isometry`](https://prove2.me/theorems/844bb102-d20e-4faf-9d4a-a819ecee9415), [`KLS/LogConcave/Regular/Poincare`](https://prove2.me/theorems/f1e79aba-37a4-40d0-a0c1-f22bee7a9127), [`KLS/LogConcave/WeakLimit`](https://prove2.me/theorems/7f87bac4-42a8-4711-b788-2d3b139d7914), [`KLS/IsotropicSupport`](https://prove2.me/theorems/0df82d3b-ac5a-45d7-a562-335edb194007), [`Poincare/SmoothTest/Comparison`](https://prove2.me/theorems/2cc5136c-e250-45ef-8770-d1af91bb9c3f).
--
--   Theorems in source order:
--
--   - [`localSlope_le_of_regular_isotropic_bound`](https://prove2.me/theorems/621a2407-818c-46e6-9957-c61bcf6e344e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean) · `FunctionalInequalities.KLS.LogConcave.IsotropicReduction` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean#L1-L137 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.IsotropicReduction`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isometry
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Poincare
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakLimit
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Comparison


