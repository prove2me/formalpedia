-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit
-- name    : KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:20:35.133995+00:00
-- url     : https://prove2.me/theorems/e4730d77-c352-491a-b178-72fb5045a2b9
-- title:
--   Import context: Poincare/SmoothTest/WeakLimit
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Poincare.SmoothTest.Basic` and `FunctionalInequalities.Analysis.Cutoff.SmoothBall`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `Mathlib.Topology.ContinuousMap.Bounded.Basic`, and `Mathlib.MeasureTheory.Integral.DominatedConvergence`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Poincare.SmoothTest.Basic
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.Topology.ContinuousMap.Bounded.Basic
--   import FunctionalInequalities.Analysis.Cutoff.SmoothBall
--   import Mathlib.MeasureTheory.Integral.DominatedConvergence
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f), [`Analysis/Cutoff/SmoothBall`](https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63).
--
--   Theorems in source order:
--
--   - [`variance_le_mul_energy_of_tendsto`](https://prove2.me/theorems/0405b112-362b-4b97-b8df-8b73697c57e3)
--   - [`Admissible.of_contDiff_hasCompactSupport`](https://prove2.me/theorems/7f79ab39-6c03-4d68-870d-2dd02d1e1b0b)
--   - [`tendsto_integral_scaled_mul`](https://prove2.me/theorems/068f0f8e-b98a-4f43-90a9-f224447633d6)
--   - [`norm_gradient_scaled_mul_sq_le`](https://prove2.me/theorems/1194b2a8-bd6e-4efd-bc86-f6b48715f7e0)
--   - [`tendsto_energy_scaled_mul`](https://prove2.me/theorems/7ebf926b-52bf-46f9-b74c-32dbc8febfcb)
--   - [`Holds.of_compactSupport`](https://prove2.me/theorems/7a878356-8017-4c9f-ae31-615b3aebf1ac)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean) · `FunctionalInequalities.Poincare.SmoothTest.WeakLimit` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L1-L598 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, import-context bundle `KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Mathlib.MeasureTheory.Integral.DominatedConvergence


