-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit
-- name    : KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:23:55.618368+00:00
-- url     : https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6
-- title:
--   Import context: LevyStochCalc/Ito/VectorItoVersionLimit
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.VectorItoVersionLimit` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Ito.VectorItoVersionUnbounded`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.VectorItoVersionUnbounded
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/VectorItoVersionUnbounded`](https://prove2.me/theorems/283f8eec-9617-48b4-836e-d610c16dd968).
--
--   Theorems in source order:
--
--   - [`le_add_inv_mul_sq`](https://prove2.me/theorems/55fc83fc-8bfe-43c9-9ba2-4e5fb4a6199b)
--   - [`clampMesh_mono_window`](https://prove2.me/theorems/17031eaf-0282-46a9-a32a-db61ccb38eec)
--   - [`exists_seq_clampMesh_window_lt`](https://prove2.me/theorems/b2eb4ef5-6631-48e3-9006-913e761e4fc6)
--   - [`vectorItoProcess_ae_eq_zero`](https://prove2.me/theorems/2c299ed7-02cc-4215-b871-f99239baed20)
--   - [`exists_isVectorItoVersion_of_unbounded`](https://prove2.me/theorems/31d4b1e5-43c0-487e-8cd2-7922775543cc)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean) · `LevyStochCalc.Ito.VectorItoVersionLimit` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L1-L520 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.VectorItoVersionLimit`, import-context bundle `KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionLimit.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionUnbounded

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


