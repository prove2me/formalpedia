-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:19:23.1715+00:00
-- url     : https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8
-- title:
--   Import context: Analysis/Matrix/Sign
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Matrix.Sign` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.Analysis.Matrix.Trace.Energy`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Matrix.Order`, `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs`, and `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Matrix.Order
--   import FunctionalInequalities.Analysis.Matrix.Trace.Energy
--   import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
--   import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Matrix/Trace/Energy`](https://prove2.me/theorems/3c755a85-5be5-4a52-9826-3a9afe9620f8).
--
--   Theorems in source order:
--
--   - [`symmetric_matrix_sqrt_real_cfc_bridge`](https://prove2.me/theorems/55e7d3a2-5447-43f2-ad4d-6d412da05abe)
--   - [`symmetric_matrix_sign_factorization`](https://prove2.me/theorems/dc2e7bc6-783c-47b2-ab0e-99d975ec6a82)
--   - [`symmetric_jordan_decomposition`](https://prove2.me/theorems/a088e571-4bf9-4eb8-9d83-6d45e8be135b)
--   - [`symmetric_matrix_spectral_geometry`](https://prove2.me/theorems/a896bf49-4875-4093-8aae-c4e196200010)
--   - [`exists_symmetric_isUnit_matrix_sequence`](https://prove2.me/theorems/2457a68a-10fc-4205-94a6-4898596c7fa3)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean) · `FunctionalInequalities.Analysis.Matrix.Sign` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L1-L439 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Matrix.Sign`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_Sign`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.Matrix.Order
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic


