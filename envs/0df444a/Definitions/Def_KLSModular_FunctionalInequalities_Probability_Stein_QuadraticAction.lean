-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction
-- name    : KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:07:22.980529+00:00
-- url     : https://prove2.me/theorems/0e4b9766-8959-44c6-bfc8-ee388e8834ba
-- title:
--   Import context: Probability/Stein/QuadraticAction
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.Stein.QuadraticAction` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Matrix.Integral`, `FunctionalInequalities.Analysis.Operator.Coordinates`, `FunctionalInequalities.Probability.Stein.Kernel`, `FunctionalInequalities.Analysis.Matrix.Sign`, and `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`. It also directly imports the external prerequisite module `Mathlib.Probability.Moments.Variance`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Matrix.Integral
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   import FunctionalInequalities.Probability.Stein.Kernel
--   import Mathlib.Probability.Moments.Variance
--   import FunctionalInequalities.Analysis.Matrix.Sign
--   import FunctionalInequalities.Analysis.Matrix.Trace.Algebra
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Matrix/Integral`](https://prove2.me/theorems/09aa8c12-3230-447e-89a1-dc642659f2aa), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e), [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8), [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee).
--
--   Theorems in source order:
--
--   - [`sum_integral_spectral_noise_energy_le`](https://prove2.me/theorems/581326c3-8b69-482f-9883-e185292234e7)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Stein/QuadraticAction.lean) · `FunctionalInequalities.Probability.Stein.QuadraticAction` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Stein/QuadraticAction.lean#L1-L200 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.Stein.QuadraticAction`, import-context bundle `KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Mathlib.Probability.Moments.Variance
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra


