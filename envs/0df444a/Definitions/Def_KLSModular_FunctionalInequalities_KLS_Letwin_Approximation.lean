-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_Approximation
-- name    : KLSModular_FunctionalInequalities_KLS_Letwin_Approximation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:01:29.622577+00:00
-- url     : https://prove2.me/theorems/6e41413b-e6b9-4497-be00-27a5ca71753a
-- title:
--   Import context: KLS/Letwin/Approximation
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.Letwin.Approximation` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.CompactReduction`, `FunctionalInequalities.KLS.LogConcave.BallConditioning`, `FunctionalInequalities.KLS.LogConcave.IsotropicReduction`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation`, `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments`, `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, `FunctionalInequalities.Probability.Conditioning`, and `FunctionalInequalities.Probability.Moments`. It also directly imports the external prerequisite module `Mathlib.Analysis.Convex.Measure`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.CompactReduction
--   import FunctionalInequalities.KLS.LogConcave.BallConditioning
--   import FunctionalInequalities.KLS.LogConcave.IsotropicReduction
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
--   import FunctionalInequalities.KLS.LogConcave.Density.Tilted
--   import FunctionalInequalities.Probability.Conditioning
--   import FunctionalInequalities.Probability.Moments
--   import Mathlib.Analysis.Convex.Measure
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`KLS/LogConcave/BallConditioning`](https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc), [`KLS/LogConcave/IsotropicReduction`](https://prove2.me/theorems/71545edb-cd76-4fa7-a5a9-f3cfaa7db601), [`KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation`](https://prove2.me/theorems/eabcdc52-c914-4c59-b1af-3d43455f910d), [`KLS/LogConcave/Density/BorellRepresentation/Moments`](https://prove2.me/theorems/e5df2dc6-6ebd-4244-bfb5-41d46b1c70d1), [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38), [`Probability/Conditioning`](https://prove2.me/theorems/b0c5089d-02c8-45e7-8c38-91aba9c55475), [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce).
--
--   Theorems in source order:
--
--   - [`exists_regularClass_seq_of_compact`](https://prove2.me/theorems/87b3bac7-94fd-4a3d-b3c3-f57d65a72c20)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean) · `FunctionalInequalities.KLS.Letwin.Approximation` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean#L1-L344 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.Letwin.Approximation`, import-context bundle `KLSModular_FunctionalInequalities_KLS_Letwin_Approximation`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Conditioning
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments
import Mathlib.Analysis.Convex.Measure


