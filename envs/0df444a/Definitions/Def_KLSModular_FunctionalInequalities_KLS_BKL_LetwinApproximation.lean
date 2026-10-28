-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_LetwinApproximation
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_LetwinApproximation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:07:48.325146+00:00
-- url     : https://prove2.me/theorems/e9cbfeb1-0297-45a7-8eb7-9cdeed00f517
-- title:
--   Import context: KLS/BKL/LetwinApproximation
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.LetwinApproximation` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Probability.Conditioning`, `FunctionalInequalities.KLS.LogConcave.BallConditioning`, `FunctionalInequalities.KLS.BKL.CompactReduction`, `FunctionalInequalities.KLS.LogConcave.IsotropicReduction`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation`, and `FunctionalInequalities.KLS.Letwin.Approximation`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Conditioning
--   import FunctionalInequalities.KLS.LogConcave.BallConditioning
--   import FunctionalInequalities.KLS.BKL.CompactReduction
--   import FunctionalInequalities.KLS.LogConcave.IsotropicReduction
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
--   import FunctionalInequalities.KLS.Letwin.Approximation
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Conditioning`](https://prove2.me/theorems/b0c5089d-02c8-45e7-8c38-91aba9c55475), [`KLS/LogConcave/BallConditioning`](https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`KLS/LogConcave/IsotropicReduction`](https://prove2.me/theorems/71545edb-cd76-4fa7-a5a9-f3cfaa7db601), [`KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation`](https://prove2.me/theorems/eabcdc52-c914-4c59-b1af-3d43455f910d), [`KLS/Letwin/Approximation`](https://prove2.me/theorems/6e41413b-e6b9-4497-be00-27a5ca71753a).
--
--   Theorems in source order:
--
--   - [`letwinCompactBound_of_regularClass`](https://prove2.me/theorems/a49dd56e-2442-4aae-a07b-6def43badd68)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean) · `FunctionalInequalities.KLS.BKL.LetwinApproximation` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean#L1-L55 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.LetwinApproximation`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_LetwinApproximation`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Conditioning
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_IsotropicReduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_Approximation


