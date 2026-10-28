-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator
-- name    : KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:10:01.094992+00:00
-- url     : https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc
-- title:
--   Import context: LevyStochCalc/Brownian/ItoL2CompletionCompensator
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoL2CompletionCompensator` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `LevyStochCalc.Brownian.ItoL2CompletionConvergence`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoL2CompletionConvergence
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoL2CompletionConvergence`](https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887).
--
--   Theorems in source order:
--
--   - [`offDiagonal_increment_integral_zero_weighted`](https://prove2.me/theorems/f2dfb111-9070-47ca-850d-5692b6155761)
--   - [`simpleIntegral_sub_eq_clamp_sum`](https://prove2.me/theorems/5b6d9d87-e4ca-4af9-8b0b-701697a48c84)
--   - [`simpleIntegral_sub_sq_bochner_clamped_weighted`](https://prove2.me/theorems/9fca8288-f73b-4ee9-a521-8212a2c93f44)
--   - [`setIntegral_eval_sq_Icc_clamped`](https://prove2.me/theorems/264a25e4-219e-44a6-9deb-bfc553ff7dd9)
--   - [`martingale_simpleIntegral_sq_sub_compensator`](https://prove2.me/theorems/76ba9e80-d221-4784-b289-e962828cbbfd)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean) · `LevyStochCalc.Brownian.ItoL2CompletionCompensator` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean#L1-L587 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


