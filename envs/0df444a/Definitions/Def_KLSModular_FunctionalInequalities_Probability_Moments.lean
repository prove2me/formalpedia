-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments
-- name    : KLSModular_FunctionalInequalities_Probability_Moments
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:33:12.01826+00:00
-- url     : https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce
-- title:
--   Import context: Probability/Moments
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.Moments` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Function.LpSeminorm.Basic`, `Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic`, `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `Mathlib.Analysis.InnerProductSpace.PiL2`, `Mathlib.Analysis.Normed.Lp.MeasurableSpace`, `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.Probability.Moments.Variance`, `Mathlib.MeasureTheory.Integral.Bochner.Set`, and `Mathlib.MeasureTheory.Measure.Real`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
--   import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.Normed.Lp.MeasurableSpace
--   import Mathlib.MeasureTheory.Integral.Bochner.Basic
--   import Mathlib.Probability.Moments.Variance
--   import Mathlib.MeasureTheory.Integral.Bochner.Set
--   import Mathlib.MeasureTheory.Measure.Real
--   import FunctionalInequalities.Analysis.Matrix.Trace.Algebra
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee).
--
--   Theorems in source order:
--
--   - [`sum_variance_entries_eq_integral_trace_sub_trace_mean`](https://prove2.me/theorems/88527e56-76ae-4a12-8518-4edc0d238008)
--   - [`memLp_quadratic_of_memLp_four`](https://prove2.me/theorems/80afcd22-0f06-48b5-88c9-0fb875897eef)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Moments.lean) · `FunctionalInequalities.Probability.Moments` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Moments.lean#L1-L585 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.Moments`, import-context bundle `KLSModular_FunctionalInequalities_Probability_Moments`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra


