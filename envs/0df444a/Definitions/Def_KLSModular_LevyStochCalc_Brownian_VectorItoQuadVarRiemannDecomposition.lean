-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:22:30.763398+00:00
-- url     : https://prove2.me/theorems/ea95ae2a-21bc-42c8-afc2-c6002d198e2b
-- title:
--   Import context: LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds`](https://prove2.me/theorems/e506e7f3-bd3b-40cf-9c41-baaea27e3be9).
--
--   Theorems in source order:
--
--   - [`vectorItoMartingale_prod_eq`](https://prove2.me/theorems/13df531e-8950-45e0-98a1-a8e79fecabcc)
--   - [`IsVectorItoVersion.quadVarRiemann_decomp_ae`](https://prove2.me/theorems/99d689e6-7b6f-456b-80a4-7810d4f01658)
--   - [`IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le`](https://prove2.me/theorems/f3fde419-4acc-40a6-83f8-e6f5d5a9c736)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean) · `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L1-L441 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition`, import-context bundle `KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


