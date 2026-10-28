-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality
-- name    : KLSModular_LevyStochCalc_Ito_PicardLocality
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:29:17.047662+00:00
-- url     : https://prove2.me/theorems/6f022361-7332-41fe-a646-6e283b2f482e
-- title:
--   Import context: LevyStochCalc/Ito/PicardLocality
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.PicardLocality` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Ito.PicardSupL2`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardSupL2
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardSupL2`](https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0).
--
--   Theorems in source order:
--
--   - [`itoIntegral_congr_ae`](https://prove2.me/theorems/5b2a8fe4-013f-4df7-9936-5da724b67c11)
--   - [`compensatedIntegral_congr_ae`](https://prove2.me/theorems/4e52f913-b0fa-453d-a760-85ac36d0bb61)
--   - [`picardStep_diffusion_congr_ae`](https://prove2.me/theorems/6c336559-f093-4ef9-8ae4-892731263519)
--   - [`picardStep_jump_congr_ae`](https://prove2.me/theorems/dbbc5d31-c9ed-480b-b61a-98ddb19cdde2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardLocality.lean) · `LevyStochCalc.Ito.PicardLocality` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardLocality.lean#L1-L317 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.PicardLocality`, import-context bundle `KLSModular_LevyStochCalc_Ito_PicardLocality`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardLocality.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


