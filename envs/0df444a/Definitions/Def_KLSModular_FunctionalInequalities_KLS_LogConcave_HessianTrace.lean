-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianTrace
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HessianTrace
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:54:04.490783+00:00
-- url     : https://prove2.me/theorems/a007d6bd-8267-4526-a1ec-a10003542850
-- title:
--   Import context: KLS/LogConcave/HessianTrace
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.HessianTrace` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb`, `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, and `FunctionalInequalities.Probability.Moments`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Matrix.Order` and `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.WeakBrascampLieb
--   import FunctionalInequalities.Analysis.Matrix.WeakDerivative
--   import FunctionalInequalities.Analysis.Matrix.Trace.Algebra
--   import FunctionalInequalities.Probability.Moments
--   import Mathlib.Analysis.Matrix.Order
--   import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/WeakBrascampLieb`](https://prove2.me/theorems/4d759700-9cad-4791-aded-7197e3d56cfa), [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681), [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee), [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce).
--
--   Theorems in source order:
--
--   - [`integral_trace_quadratic_le_two_mul_trace_sq`](https://prove2.me/theorems/0915019c-ff4d-443b-bb7e-f4eeece90338)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianTrace.lean) · `FunctionalInequalities.KLS.LogConcave.HessianTrace` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HessianTrace.lean#L1-L292 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.HessianTrace`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HessianTrace`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic


