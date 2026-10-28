-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:18:22.347032+00:00
-- url     : https://prove2.me/theorems/d5560108-f34d-426e-87a5-851045a6e923
-- title:
--   Import context: KLS/LogConcave/Density/GaussianSmoothing/Approximation
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Integral.PeakFunction`, `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`, `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`, `Mathlib.MeasureTheory.Integral.DominatedConvergence`, `Mathlib.MeasureTheory.Integral.Bochner.Set`, `Mathlib.Topology.ContinuousMap.Bounded.Normed`, and `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
--   import Mathlib.MeasureTheory.Integral.PeakFunction
--   import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
--   import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
--   import Mathlib.MeasureTheory.Integral.DominatedConvergence
--   import Mathlib.MeasureTheory.Integral.Bochner.Set
--   import Mathlib.Topology.ContinuousMap.Bounded.Normed
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Theorems in source order:
--
--   - [`normalizedDensity_tendsto_L1`](https://prove2.me/theorems/c0a6720b-acb6-4b57-b8ed-118a32ffd64b)
--   - [`smoothedLaw_integral_bounded_tendsto`](https://prove2.me/theorems/0594eb14-470e-44f6-ba57-66325d98a696)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Approximation.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Approximation.lean#L1-L355 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Approximation`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


