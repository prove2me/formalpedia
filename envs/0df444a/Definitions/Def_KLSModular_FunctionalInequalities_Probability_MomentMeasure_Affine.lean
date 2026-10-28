-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine
-- name    : KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:58:19.706854+00:00
-- url     : https://prove2.me/theorems/763df6ce-b81b-47cb-8b6b-d4d0c79b4571
-- title:
--   Import context: Probability/MomentMeasure/Affine
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.MomentMeasure.Affine` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Convex.Affine`, `FunctionalInequalities.Probability.MomentMeasure.Integrability`, and `FunctionalInequalities.Probability.MomentMeasure.Basic`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Group.LIntegral`, `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace`, and `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Affine
--   import FunctionalInequalities.Probability.MomentMeasure.Integrability
--   import FunctionalInequalities.Probability.MomentMeasure.Basic
--   import Mathlib.MeasureTheory.Group.LIntegral
--   import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
--   import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Affine`](https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c), [`Probability/MomentMeasure/Integrability`](https://prove2.me/theorems/0f56c51b-1f88-4bf0-b556-0b95a64eb739), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Theorems in source order:
--
--   - [`affineSubtract_potentialIntegrable`](https://prove2.me/theorems/f9035aa8-a93c-47ed-80fb-13efe5d1963a)
--   - [`integral_affineSubtract`](https://prove2.me/theorems/b464f0e5-346a-4249-bc07-ab1613a70aef)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean) · `FunctionalInequalities.Probability.MomentMeasure.Affine` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L1-L176 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.MomentMeasure.Affine`, import-context bundle `KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


