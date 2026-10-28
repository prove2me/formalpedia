-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:25:25.073092+00:00
-- url     : https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681
-- title:
--   Import context: Analysis/Matrix/WeakDerivative
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Matrix.WeakDerivative` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, and `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`. It also directly imports the external prerequisite module `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   import FunctionalInequalities.Analysis.Matrix.Trace.Algebra
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5), [`Analysis/Matrix/Trace/Algebra`](https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee).
--
--   Theorems in source order:
--
--   - [`hasWeakDerivAlong_det_of_locally_memLp_two`](https://prove2.me/theorems/33254f42-0c89-459e-bcd2-427b387a0099)
--   - [`hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`](https://prove2.me/theorems/2e62203f-0ffc-4c8e-8f06-055bcb5ac5d9)
--   - [`ae_weak_matrix_inverse_derivative`](https://prove2.me/theorems/d6fe03d3-18d4-4ee9-8216-cfc3ec407a97)
--   - [`bounded_trace_quadratic_weak_derivative_data`](https://prove2.me/theorems/cc2fdc63-2222-4fdb-85c7-4532eb76bc0c)
--   - [`bounded_weak_matrix_product_entry`](https://prove2.me/theorems/3c19e2fb-eb53-4358-81de-489fd6539c03)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean) · `FunctionalInequalities.Analysis.Matrix.WeakDerivative` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L1-L325 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra


