-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTaylor
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoTaylor
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:12:58.406017+00:00
-- url     : https://prove2.me/theorems/e2f63476-dcbb-4f48-b908-f9b176dad140
-- title:
--   Import context: LevyStochCalc/Brownian/VectorItoTaylor
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.VectorItoTaylor` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.VectorItoThirdMoment` and `LevyStochCalc.Brownian.TaylorTwoModulus`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoThirdMoment
--   import LevyStochCalc.Brownian.TaylorTwoModulus
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoThirdMoment`](https://prove2.me/theorems/a91256d3-896e-401f-8609-adb538add313), [`LevyStochCalc/Brownian/TaylorTwoModulus`](https://prove2.me/theorems/9de0d95a-7af7-4d8b-902e-7044b67e5df2).
--
--   Theorems in source order:
--
--   - [`measurable_taylorRemainderNormed`](https://prove2.me/theorems/82f77efa-c25f-4464-bcbe-e2c70b974c2c)
--   - [`sum_integral_sq_norm_vectorItoIncrement_le`](https://prove2.me/theorems/f8183882-c470-441e-b8d8-7efc9444036e)
--   - [`integral_abs_vectorTaylorRemainder_le_affine`](https://prove2.me/theorems/c50f87d4-01af-4809-9de8-adef3412ad18)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoTaylor.lean) · `LevyStochCalc.Brownian.VectorItoTaylor` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoTaylor.lean#L1-L206 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.VectorItoTaylor`, import-context bundle `KLSModular_LevyStochCalc_Brownian_VectorItoTaylor`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoTaylor.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTaylor.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


