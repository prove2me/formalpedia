-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums
-- name    : KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:56:35.106147+00:00
-- url     : https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322
-- title:
--   Import context: LevyStochCalc/Brownian/ItoFourthMomentPartialSums
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.ItoFourthMomentIncrements`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoFourthMomentIncrements
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3).
--
--   Theorems in source order:
--
--   - [`integral_add_mul_increment_sq`](https://prove2.me/theorems/d77376ee-50f5-4d6a-b971-007d80feac97)
--   - [`integral_add_mul_increment_pow_four`](https://prove2.me/theorems/70cfa191-ba5b-406e-9b47-0bc6e678c599)
--   - [`integral_partialSum_sq_succ`](https://prove2.me/theorems/9bf4edcb-e687-4a69-83b1-87842c0ed837)
--   - [`integral_partialSum_pow_four_succ`](https://prove2.me/theorems/8d6ebf13-04ca-46c7-8946-0ee73126e99a)
--   - [`integral_partialSum_sq_le_varClock`](https://prove2.me/theorems/2ab4ca54-1962-4f62-bd70-5633cdf86d27)
--   - [`integral_partialSum_pow_four_le_varClock`](https://prove2.me/theorems/81999667-558b-4b27-9df9-47bbd1eb2a2d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean) · `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean#L1-L543 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoFourthMomentPartialSums`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


