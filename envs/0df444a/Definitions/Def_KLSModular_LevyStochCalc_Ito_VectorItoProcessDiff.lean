-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff
-- name    : KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:06:07.843381+00:00
-- url     : https://prove2.me/theorems/cd1eb156-9d40-4d90-80b1-58b54714509a
-- title:
--   Import context: LevyStochCalc/Ito/VectorItoProcessDiff
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.VectorItoProcessDiff` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.ItoTruncate` and `LevyStochCalc.Ito.PicardOutput`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoTruncate
--   import LevyStochCalc.Ito.PicardOutput
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoTruncate`](https://prove2.me/theorems/7275d4a0-b19e-41be-9f18-49283c27276a), [`LevyStochCalc/Ito/PicardOutput`](https://prove2.me/theorems/ca9e943e-6d8f-4bae-90ca-7ae7b86fdd63).
--
--   Theorems in source order:
--
--   - [`lintegral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/868b1ad2-f913-46c1-9da7-a8c67dc44c11)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoProcessDiff.lean) · `LevyStochCalc.Ito.VectorItoProcessDiff` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoProcessDiff.lean#L1-L194 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.VectorItoProcessDiff`, import-context bundle `KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoProcessDiff.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardOutput

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoProcessDiff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


