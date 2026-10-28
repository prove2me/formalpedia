-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus
-- name    : KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:56:15.505243+00:00
-- url     : https://prove2.me/theorems/9de0d95a-7af7-4d8b-902e-7044b67e5df2
-- title:
--   Import context: LevyStochCalc/Brownian/TaylorTwoModulus
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.TaylorTwoModulus` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.TaylorTwoVector`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.TaylorTwoVector
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/TaylorTwoVector`](https://prove2.me/theorems/7b95962e-e11d-4fe9-a26b-01c2fa7c2715).
--
--   Theorems in source order:
--
--   - [`abs_sub_taylor_one_le_modulus`](https://prove2.me/theorems/039f7378-37a4-4a18-99b1-faedf7580c7d)
--   - [`abs_sub_taylor_two_le_modulus`](https://prove2.me/theorems/9288cfbc-c843-4593-aa84-85c99c8a03f2)
--   - [`abs_sub_taylor_two_le_modulus_normed`](https://prove2.me/theorems/3f74f0d8-d72e-475d-8cd1-7e869d226dff)
--   - [`abs_sub_taylor_two_le_affine`](https://prove2.me/theorems/5ef92fc9-92b2-4b92-8d3b-5f15ef4f7c9a)
--   - [`abs_taylorRemainderNormed_le_affine`](https://prove2.me/theorems/be72e992-5b1b-4081-98f2-f215cb884717)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/TaylorTwoModulus.lean) · `LevyStochCalc.Brownian.TaylorTwoModulus` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/TaylorTwoModulus.lean#L1-L187 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.TaylorTwoModulus`, import-context bundle `KLSModular_LevyStochCalc_Brownian_TaylorTwoModulus`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/TaylorTwoModulus.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_TaylorTwoVector

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/TaylorTwoModulus.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


