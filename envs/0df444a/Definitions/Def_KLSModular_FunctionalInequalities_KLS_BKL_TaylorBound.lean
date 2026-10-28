-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:14:13.565051+00:00
-- url     : https://prove2.me/theorems/ef8651c6-ddf2-4f86-883a-e9e4c00f2d13
-- title:
--   Import context: KLS/BKL/TaylorBound
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.TaylorBound` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.BKL.Suspension.Density`, `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, `FunctionalInequalities.KLS.BKL.Suspension.Derivatives`, `FunctionalInequalities.KLS.BKL.Suspension.Moments`, `FunctionalInequalities.KLS.LogConcave.Regular.Basic`, `FunctionalInequalities.Analysis.BakryEmery.Calculus`, `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, `FunctionalInequalities.L2.AffineDecomposition`, and `FunctionalInequalities.KLS.BKL.Suspension.Law`. It also directly imports the external prerequisite module `Mathlib.Analysis.Normed.Lp.SmoothApprox`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Suspension.Density
--   import FunctionalInequalities.KLS.BKL.Suspension.Cumulant
--   import FunctionalInequalities.KLS.BKL.Suspension.Derivatives
--   import FunctionalInequalities.KLS.BKL.Suspension.Moments
--   import FunctionalInequalities.KLS.LogConcave.Regular.Basic
--   import Mathlib.Analysis.Normed.Lp.SmoothApprox
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
--   import FunctionalInequalities.L2.AffineDecomposition
--   import FunctionalInequalities.KLS.BKL.Suspension.Law
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Suspension/Density`](https://prove2.me/theorems/34f067f9-b370-4131-a2be-776da314cea2), [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b), [`KLS/BKL/Suspension/Derivatives`](https://prove2.me/theorems/3fa39843-9f8d-446f-806f-25b47f8ada2b), [`KLS/BKL/Suspension/Moments`](https://prove2.me/theorems/bb78b4a9-f1ce-44b8-9c83-f67999cad00c), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5), [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614), [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3).
--
--   Theorems in source order:
--
--   - [`norm_coordTensor_taylorTensor_sq_le_of_smooth`](https://prove2.me/theorems/ad272b35-4fb6-4f10-b3ea-e0b98ec982a2)
--   - [`norm_coordTensor_taylorTensor_sq_le_two_mul`](https://prove2.me/theorems/b022259f-6e00-41ce-bbc5-b1bff64f4b1e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean) · `FunctionalInequalities.KLS.BKL.TaylorBound` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean#L1-L587 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.TaylorBound`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law


