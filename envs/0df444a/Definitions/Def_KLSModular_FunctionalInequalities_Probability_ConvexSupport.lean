-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
-- name    : KLSModular_FunctionalInequalities_Probability_ConvexSupport
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:56:57.950124+00:00
-- url     : https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e
-- title:
--   Import context: Probability/ConvexSupport
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.ConvexSupport` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Analysis.InnerProductSpace.Basic`, `Mathlib.Analysis.InnerProductSpace.Continuous`, `Mathlib.Analysis.Normed.Module.FiniteDimension`, `Mathlib.Analysis.Convex.Hull`, `Mathlib.Analysis.Convex.Topology`, `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `Mathlib.MeasureTheory.Measure.Support`, `Mathlib.Topology.Order.Compact`, `Mathlib.Analysis.Normed.Affine.AddTorsorBases`, `Mathlib.MeasureTheory.Integral.Lebesgue.Markov`, `Mathlib.Data.EReal.Operations`, `Mathlib.Analysis.Convex.Continuous`, `Mathlib.Analysis.LocallyConvex.Separation`, `Mathlib.Analysis.InnerProductSpace.Dual`, `Mathlib.MeasureTheory.Integral.Bochner.Basic`, and `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.Basic
--   import Mathlib.Analysis.InnerProductSpace.Continuous
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.Analysis.Convex.Hull
--   import Mathlib.Analysis.Convex.Topology
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.MeasureTheory.Measure.Support
--   import Mathlib.Topology.Order.Compact
--   import Mathlib.Analysis.Normed.Affine.AddTorsorBases
--   import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
--   import Mathlib.Data.EReal.Operations
--   import Mathlib.Analysis.Convex.Continuous
--   import Mathlib.Analysis.LocallyConvex.Separation
--   import Mathlib.Analysis.InnerProductSpace.Dual
--   import Mathlib.MeasureTheory.Integral.Bochner.Basic
--   import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`exists_mem_support_inner_sub_pos_of_mem_interior_convexHull`](https://prove2.me/theorems/95ce23ed-65af-442a-8f05-c357dc1dfec1)
--   - [`exists_pos_ball_inner_sub_pos_of_mem_support`](https://prove2.me/theorems/f71df184-ee7e-48db-81fc-c3549dfdd128)
--   - [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support`](https://prove2.me/theorems/b1dc5e60-c703-4418-988d-32b752eb87e5)
--   - [`mem_interior_setOf_ne_top_of_lintegral_ne_top`](https://prove2.me/theorems/41e08c8a-6e29-45a9-8d48-c23b3f6ab84d)
--   - [`exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure`](https://prove2.me/theorems/2e3067a3-8fdf-4402-9d95-d8eb776cd1f3)
--   - [`real_convexOn_effective_domain`](https://prove2.me/theorems/f7c7760e-e128-40c5-a6ce-efaac3655fcc)
--   - [`strict_sublevel_convex_and_interior`](https://prove2.me/theorems/463b9839-1217-4882-805b-3a7aca81934e)
--   - [`exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`](https://prove2.me/theorems/47effa70-14be-45e1-bd3e-85ca90620000)
--   - [`zero_mem_interior_convexHull_support_of_integral_eq_zero`](https://prove2.me/theorems/24d566b9-c33c-4ef2-a315-a7ad900693e2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean) · `FunctionalInequalities.Probability.ConvexSupport` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L1-L778 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.ConvexSupport`, import-context bundle `KLSModular_FunctionalInequalities_Probability_ConvexSupport`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


