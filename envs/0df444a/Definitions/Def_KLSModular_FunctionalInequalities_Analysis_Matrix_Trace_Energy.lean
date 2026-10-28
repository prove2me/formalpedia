-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:18:59.249992+00:00
-- url     : https://prove2.me/theorems/3c755a85-5be5-4a52-9826-3a9afe9620f8
-- title:
--   Import context: Analysis/Matrix/Trace/Energy
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Matrix.Trace.Energy` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.Analysis.Matrix.Trace.Power`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`, `Mathlib.Analysis.Matrix.PosDef`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Algebra.Order.Chebyshev`, `Mathlib.Analysis.Matrix.Order`, and `Mathlib.Tactic.NoncommRing`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
--   import Mathlib.Analysis.Matrix.PosDef
--   import Mathlib.Analysis.SpecialFunctions.Pow.Real
--   import Mathlib.Algebra.Order.Chebyshev
--   import Mathlib.Analysis.Matrix.Order
--   import Mathlib.Tactic.NoncommRing
--   import FunctionalInequalities.Analysis.Matrix.Trace.Power
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Matrix/Trace/Power`](https://prove2.me/theorems/dacdf9e6-5e72-4350-bea3-13b172a49586).
--
--   Theorems in source order:
--
--   - [`trace_energy_nonneg`](https://prove2.me/theorems/1ddd2a2c-ff85-499e-a245-832c9fd056bb)
--   - [`jordan_trace_domination`](https://prove2.me/theorems/a6423829-e14f-4879-bca7-f5ac02b2f042)
--   - [`letwin_trace_weighted_slices`](https://prove2.me/theorems/a517441b-78a2-4418-90ee-2e5a6b365cc7)
--   - [`letwin_tensor_trace_identity`](https://prove2.me/theorems/fae84bdf-a098-4054-b01e-b2eb219e86ec)
--   - [`letwin_tensor_comparison`](https://prove2.me/theorems/6e239757-a405-483f-bb98-9824d874a734)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean) · `FunctionalInequalities.Analysis.Matrix.Trace.Energy` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean#L1-L453 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Matrix.Trace.Energy`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Power


