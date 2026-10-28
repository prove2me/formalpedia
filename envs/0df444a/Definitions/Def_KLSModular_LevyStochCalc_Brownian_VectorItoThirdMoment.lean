-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:12:06.235153+00:00
-- url     : https://prove2.me/theorems/a91256d3-896e-401f-8609-adb538add313
-- title:
--   Import context: LevyStochCalc/Brownian/VectorItoThirdMoment
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.VectorItoThirdMoment` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.VectorItoProcess` and `LevyStochCalc.Brownian.ItoFormulaGrid`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoProcess
--   import LevyStochCalc.Brownian.ItoFormulaGrid
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f).
--
--   Theorems in source order:
--
--   - [`integral_abs_sum_pow_three_le`](https://prove2.me/theorems/8e2176da-9942-4d76-ae35-887c676c9109)
--   - [`integral_norm_pi_pow_three_le`](https://prove2.me/theorems/5d6166a6-3ea2-4998-af8d-3304ea548177)
--   - [`integral_abs_vectorItoMartingale_sub_pow_three_le`](https://prove2.me/theorems/e79302a4-4518-490f-9961-50ba76dc4c8d)
--   - [`integral_abs_vectorItoProcess_sub_pow_three_le`](https://prove2.me/theorems/9000ae3c-ebf5-4d65-99b6-1c5389e78b62)
--   - [`integral_norm_vectorItoProcess_sub_pow_three_le`](https://prove2.me/theorems/a915718b-cb1c-4845-86c4-9351dbb6b27e)
--   - [`sum_integral_norm_vectorItoIncrement_pow_three_le`](https://prove2.me/theorems/9aa04438-e208-4383-a2ac-b7d722c248ed)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoThirdMoment.lean) · `LevyStochCalc.Brownian.VectorItoThirdMoment` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoThirdMoment.lean#L1-L235 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.VectorItoThirdMoment`, import-context bundle `KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoThirdMoment.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


