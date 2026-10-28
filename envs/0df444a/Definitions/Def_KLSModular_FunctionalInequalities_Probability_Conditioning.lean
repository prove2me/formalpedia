-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Conditioning
-- name    : KLSModular_FunctionalInequalities_Probability_Conditioning
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:08:25.231581+00:00
-- url     : https://prove2.me/theorems/b0c5089d-02c8-45e7-8c38-91aba9c55475
-- title:
--   Import context: Probability/Conditioning
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.Conditioning` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.Probability.Moments`. It also directly imports the external prerequisite modules `Mathlib.Probability.ConditionalProbability`, `Mathlib.MeasureTheory.Integral.DominatedConvergence`, `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, and `Mathlib.MeasureTheory.Measure.Portmanteau`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Moments
--   import Mathlib.Probability.ConditionalProbability
--   import Mathlib.MeasureTheory.Integral.DominatedConvergence
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.MeasureTheory.Measure.Portmanteau
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce).
--
--   Theorems in source order:
--
--   - [`tendsto_integral_cond_closedBall`](https://prove2.me/theorems/c2606332-9d4e-4a66-896d-a32140388362)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Conditioning.lean) · `FunctionalInequalities.Probability.Conditioning` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Conditioning.lean#L1-L484 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.Conditioning`, import-context bundle `KLSModular_FunctionalInequalities_Probability_Conditioning`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau


