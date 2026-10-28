-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess
-- name    : KLSModular_LevyStochCalc_Brownian_ItoProcess
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:08:32.13236+00:00
-- url     : https://prove2.me/theorems/0e852a7e-a66b-4b2e-af71-2e5817bdbfa8
-- title:
--   Import context: LevyStochCalc/Brownian/ItoProcess
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoProcess` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.DriftIncrement`, `LevyStochCalc.Brownian.ItoIncrementMoment`, and `LevyStochCalc.Probability.AbsMoment`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.DriftIncrement
--   import LevyStochCalc.Brownian.ItoIncrementMoment
--   import LevyStochCalc.Probability.AbsMoment
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/DriftIncrement`](https://prove2.me/theorems/46f140f5-271c-46b4-a62d-8c251e00fc2b), [`LevyStochCalc/Brownian/ItoIncrementMoment`](https://prove2.me/theorems/9d2f693b-1d18-45b2-b295-411fcadbdbe2), [`LevyStochCalc/Probability/AbsMoment`](https://prove2.me/theorems/a47bc9f6-36f4-49ba-b8be-98961f4f3386).
--
--   Theorems in source order:
--
--   - [`integrable_abs_drift_pow`](https://prove2.me/theorems/a6288035-95df-498a-8432-a20089aba59f)
--   - [`integral_abs_sub_stochasticIntegral_le`](https://prove2.me/theorems/b9104289-b232-47cf-94d1-9015281546b4)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoProcess.lean) · `LevyStochCalc.Brownian.ItoProcess` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoProcess.lean#L1-L344 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoProcess`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoProcess`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoProcess.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMoment
import Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


