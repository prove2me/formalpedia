-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:17:56.729982+00:00
-- url     : https://prove2.me/theorems/e506e7f3-bd3b-40cf-9c41-baaea27e3be9
-- title:
--   Import context: LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.VectorItoTimeRiemann`, `LevyStochCalc.Brownian.CrossVariationSum`, `LevyStochCalc.Brownian.PolarisedQuadVar`, and `LevyStochCalc.Probability.AbsMoment`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoTimeRiemann
--   import LevyStochCalc.Brownian.CrossVariationSum
--   import LevyStochCalc.Brownian.PolarisedQuadVar
--   import LevyStochCalc.Probability.AbsMoment
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoTimeRiemann`](https://prove2.me/theorems/ca4d7cff-196a-4a66-a466-8bfacc2957bb), [`LevyStochCalc/Brownian/CrossVariationSum`](https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c), [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f), [`LevyStochCalc/Probability/AbsMoment`](https://prove2.me/theorems/a47bc9f6-36f4-49ba-b8be-98961f4f3386).
--
--   Theorems in source order:
--
--   - [`integral_abs_weighted_cellSum_le`](https://prove2.me/theorems/e11cf57f-a8a1-490b-8ae1-d5f30200235a)
--   - [`IsVectorItoVersion.integral_abs_sum_drift_sq_le`](https://prove2.me/theorems/23639e5d-857a-4a6f-b70d-931626366848)
--   - [`IsVectorItoVersion.integral_abs_sum_driftCross_le`](https://prove2.me/theorems/99d8a7b4-fa07-42fc-9e39-4441e680b3f8)
--   - [`IsVectorItoVersion.integral_abs_sum_polarQuadVar_le`](https://prove2.me/theorems/015954d3-b039-4b49-87c9-35a017fa7c3b)
--   - [`IsVectorItoVersion.integral_abs_sum_offDiagCross_le`](https://prove2.me/theorems/fedb1c53-feeb-4afa-893e-6fa8c0db0d02)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean) · `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L1-L386 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds`, import-context bundle `KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTimeRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariationSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


