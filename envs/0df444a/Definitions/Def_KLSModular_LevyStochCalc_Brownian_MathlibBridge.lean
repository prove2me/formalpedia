-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
-- name    : KLSModular_LevyStochCalc_Brownian_MathlibBridge
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:45:55.292005+00:00
-- url     : https://prove2.me/theorems/9c49c388-9f09-41ff-9ebc-160632911f8f
-- title:
--   Import context: LevyStochCalc/Brownian/MathlibBridge
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.MathlibBridge` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.Existence`. It also directly imports the external prerequisite module `Mathlib.Probability.BrownianMotion.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Existence
--   import Mathlib.Probability.BrownianMotion.Basic
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Existence`](https://prove2.me/theorems/10f8be28-ef23-4221-869d-2a746f8fe042).
--
--   Theorems in source order:
--
--   - [`iIndep_of_indep_biSup_lt`](https://prove2.me/theorems/c904fc1b-c73f-4ae0-9449-c0e3258cf518)
--   - [`hasLaw_eval`](https://prove2.me/theorems/1fb6389e-a58c-4dab-9daf-eb1e551698b4)
--   - [`hasIndepIncrements`](https://prove2.me/theorems/f0b8f3c6-ac2e-4258-a88e-246cc3460201)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/MathlibBridge.lean) · `LevyStochCalc.Brownian.MathlibBridge` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/MathlibBridge.lean#L1-L179 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.MathlibBridge`, import-context bundle `KLSModular_LevyStochCalc_Brownian_MathlibBridge`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/MathlibBridge.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
import Mathlib.Probability.BrownianMotion.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MathlibBridge.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


