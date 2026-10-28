-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness
-- name    : KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:58:57.887993+00:00
-- url     : https://prove2.me/theorems/cbdff6c6-a5ae-41ee-946b-9f0ca1da6699
-- title:
--   Import context: Probability/MomentMeasure/Compactness
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.MomentMeasure.Compactness` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Probability.ConvexSupport`, `FunctionalInequalities.Analysis.Convex.PointwiseCompactness`, `FunctionalInequalities.Analysis.Convex.RadialExtension`, and `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Integral.Lebesgue.Add`, `Mathlib.MeasureTheory.Integral.IntegrableOn`, `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`, and `Mathlib.Topology.Instances.EReal.Lemmas`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.ConvexSupport
--   import FunctionalInequalities.Analysis.Convex.PointwiseCompactness
--   import FunctionalInequalities.Analysis.Convex.RadialExtension
--   import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
--   import Mathlib.MeasureTheory.Integral.Lebesgue.Add
--   import Mathlib.MeasureTheory.Integral.IntegrableOn
--   import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
--   import Mathlib.Topology.Instances.EReal.Lemmas
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e), [`Analysis/Convex/PointwiseCompactness`](https://prove2.me/theorems/566d2f2b-855b-42e3-83d2-9a81960cbc41), [`Analysis/Convex/RadialExtension`](https://prove2.me/theorems/da2489dd-75ed-4659-a13a-f2ad3f5ccb75), [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Theorems in source order:
--
--   - [`exists_subseq_lintegral_le_liminf_of_convex_epigraph`](https://prove2.me/theorems/27a45796-950c-4905-a61b-2943ad71aab6)
--   - [`exists_subseq_integral_bounds_of_convex_epigraph`](https://prove2.me/theorems/475ba44f-a554-43ce-bfd2-ddb53b1e5734)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean) · `FunctionalInequalities.Probability.MomentMeasure.Compactness` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L1-L286 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.MomentMeasure.Compactness`, import-context bundle `KLSModular_FunctionalInequalities_Probability_MomentMeasure_Compactness`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_PointwiseCompactness
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas


