-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:55:20.077212+00:00
-- url     : https://prove2.me/theorems/4063692a-a203-477a-8815-ef391dc73f51
-- title:
--   Import context: Analysis/Matrix/LogDet
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Matrix.LogDet` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Analysis.Matrix.PosDef`, `Mathlib.Analysis.Matrix.Order`, `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`, `Mathlib.Analysis.SpecialFunctions.Log.Deriv`, `Mathlib.Analysis.Calculus.Deriv.Inv`, `Mathlib.Analysis.Convex.Deriv`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Analysis.Matrix.Spectrum`, and `Mathlib.LinearAlgebra.Matrix.Trace`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Matrix.PosDef
--   import Mathlib.Analysis.Matrix.Order
--   import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
--   import Mathlib.Analysis.SpecialFunctions.Log.Deriv
--   import Mathlib.Analysis.Calculus.Deriv.Inv
--   import Mathlib.Analysis.Convex.Deriv
--   import Mathlib.Analysis.SpecialFunctions.Pow.Real
--   import Mathlib.Analysis.Matrix.Spectrum
--   import Mathlib.LinearAlgebra.Matrix.Trace
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`forall_posDef_add_log_det_le_trace_iff`](https://prove2.me/theorems/99f67c0b-fea3-4671-8e5b-e62a896aa733)
--   - [`scalar_log_gap`](https://prove2.me/theorems/048f38d9-1535-47f8-a190-2a68f7a7a501)
--   - [`log_det_add_frobenius_sq_le`](https://prove2.me/theorems/42e7e2e1-c8f2-4cb8-b154-81b11d6da306)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean) · `FunctionalInequalities.Analysis.Matrix.LogDet` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L1-L558 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Matrix.LogDet`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace


