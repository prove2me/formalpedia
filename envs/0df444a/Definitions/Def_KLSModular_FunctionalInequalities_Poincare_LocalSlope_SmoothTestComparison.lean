-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison
-- name    : KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:37:17.694519+00:00
-- url     : https://prove2.me/theorems/1ad07877-0369-4792-9877-1dd2997c7c22
-- title:
--   Import context: Poincare/LocalSlope/SmoothTestComparison
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation`, `FunctionalInequalities.Poincare.LocalSlope.Basic`, `FunctionalInequalities.Energy.LocalSlope.Gradient`, and `FunctionalInequalities.Poincare.SmoothTest.Comparison`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Calculus.ContDiff.RCLike` and `Mathlib.MeasureTheory.Function.LpSpace.Complete`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation
--   import FunctionalInequalities.Poincare.LocalSlope.Basic
--   import FunctionalInequalities.Energy.LocalSlope.Gradient
--   import FunctionalInequalities.Poincare.SmoothTest.Comparison
--   import Mathlib.Analysis.Calculus.ContDiff.RCLike
--   import Mathlib.MeasureTheory.Function.LpSpace.Complete
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Euclidean/LipschitzApproximation/Approximation`](https://prove2.me/theorems/f8e5c4c5-238b-4e84-9e52-3dadb9d28961), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1), [`Energy/LocalSlope/Gradient`](https://prove2.me/theorems/d01ba6e3-090e-46a3-a175-38f38d850838), [`Poincare/SmoothTest/Comparison`](https://prove2.me/theorems/2cc5136c-e250-45ef-8770-d1af91bb9c3f).
--
--   Theorems in source order:
--
--   - [`holds_iff_localSlope`](https://prove2.me/theorems/80f4b23b-124c-49c3-a604-c5a3355c1bc0)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LocalSlope/SmoothTestComparison.lean) · `FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LocalSlope/SmoothTestComparison.lean#L1-L217 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison`, import-context bundle `KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Comparison
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LpSpace.Complete


