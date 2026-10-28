-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:32:52.725121+00:00
-- url     : https://prove2.me/theorems/c47d46be-97ad-44e9-b115-414026fcb4ee
-- title:
--   Import context: Analysis/Matrix/Trace/Algebra
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Data.Real.Basic`, `Mathlib.LinearAlgebra.Matrix.Symmetric`, `Mathlib.LinearAlgebra.Matrix.Trace`, `Mathlib.Algebra.Order.Chebyshev`, `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`, `Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Positivity`, and `Mathlib.Tactic.Linarith`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Data.Real.Basic
--   import Mathlib.LinearAlgebra.Matrix.Symmetric
--   import Mathlib.LinearAlgebra.Matrix.Trace
--   import Mathlib.Algebra.Order.Chebyshev
--   import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
--   import Mathlib.Tactic.NoncommRing
--   import Mathlib.Tactic.Positivity
--   import Mathlib.Tactic.Linarith
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`trace_mul_mul_mul_eq_sum`](https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75)
--   - [`sum_matrix_product_entry_mul_eq_trace`](https://prove2.me/theorems/3c931abe-bff8-4022-a4df-7236818e79cd)
--   - [`sum_matrix_product_entry_quadratic_eq_trace`](https://prove2.me/theorems/d887a248-417a-44cd-bedd-9dbc45f1c640)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean) · `FunctionalInequalities.Analysis.Matrix.Trace.Algebra` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean#L1-L233 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Matrix.Trace.Algebra`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Algebra`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith


