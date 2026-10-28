-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2
-- name    : KLSModular_LevyStochCalc_Ito_PicardSupL2
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:15:55.087727+00:00
-- url     : https://prove2.me/theorems/95956ab0-48db-4ddd-b1af-58707e5784c0
-- title:
--   Import context: LevyStochCalc/Ito/PicardSupL2
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Ito.PicardSupL2` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Ito.PicardContraction` and `LevyStochCalc.Probability.DoobContinuous`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardContraction
--   import LevyStochCalc.Probability.DoobContinuous
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardContraction`](https://prove2.me/theorems/cb4489cb-7077-46fc-b6b1-68f031085bbb), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Theorems in source order:
--
--   - [`iSup_dyadicRunMax_drift_le`](https://prove2.me/theorems/97da484f-4fa0-43bd-b65b-1daac09db530)
--   - [`lintegral_sq_drift_bound_lt_top`](https://prove2.me/theorems/db81078a-b990-4c25-b393-aaade629f920)
--   - [`lintegral_sq_iSup_diffusion_lt_top`](https://prove2.me/theorems/bf146c9c-9e76-4873-bd21-1130aac77e2a)
--   - [`lintegral_sq_iSup_picardStep_lt_top`](https://prove2.me/theorems/d29e9d50-932e-426b-8307-33a15070eb09)
--   - [`lintegral_sq_iSup_picardSelfMapRaw_lt_top`](https://prove2.me/theorems/41b19c73-2054-4724-85c9-087eb1b0c354)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean) · `LevyStochCalc.Ito.PicardSupL2` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardSupL2.lean#L1-L403 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Ito.PicardSupL2`, import-context bundle `KLSModular_LevyStochCalc_Ito_PicardSupL2`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardSupL2.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContraction
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSupL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


