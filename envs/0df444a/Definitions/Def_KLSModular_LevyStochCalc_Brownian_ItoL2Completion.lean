-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2Completion
-- name    : KLSModular_LevyStochCalc_Brownian_ItoL2Completion
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:21:37.429643+00:00
-- url     : https://prove2.me/theorems/15202148-c170-44c6-9af7-b9de285595f1
-- title:
--   Import context: LevyStochCalc/Brownian/ItoL2Completion
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Brownian.ItoL2Completion` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `LevyStochCalc.Brownian.ItoL2CompletionLp`, `LevyStochCalc.Brownian.ItoL2CompletionExistence`, `LevyStochCalc.Brownian.ItoL2CompletionIncrement`, `LevyStochCalc.Brownian.ItoL2CompletionConvergence`, `LevyStochCalc.Brownian.ItoL2CompletionCompensator`, `LevyStochCalc.Brownian.ItoL2CompletionMaster`, `LevyStochCalc.Brownian.ItoL2CompletionQuadVar`, and `LevyStochCalc.Brownian.ItoL2CompletionApi`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoL2CompletionLp
--   import LevyStochCalc.Brownian.ItoL2CompletionExistence
--   import LevyStochCalc.Brownian.ItoL2CompletionIncrement
--   import LevyStochCalc.Brownian.ItoL2CompletionConvergence
--   import LevyStochCalc.Brownian.ItoL2CompletionCompensator
--   import LevyStochCalc.Brownian.ItoL2CompletionMaster
--   import LevyStochCalc.Brownian.ItoL2CompletionQuadVar
--   import LevyStochCalc.Brownian.ItoL2CompletionApi
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoL2CompletionLp`](https://prove2.me/theorems/4aa3ab04-3958-47e7-870f-6b1a325ace99), [`LevyStochCalc/Brownian/ItoL2CompletionExistence`](https://prove2.me/theorems/9727ce0e-a8ed-421f-8cc3-bd27f99d9261), [`LevyStochCalc/Brownian/ItoL2CompletionIncrement`](https://prove2.me/theorems/32aee3b1-b8a1-4c27-9868-1b8897f31160), [`LevyStochCalc/Brownian/ItoL2CompletionConvergence`](https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887), [`LevyStochCalc/Brownian/ItoL2CompletionCompensator`](https://prove2.me/theorems/11b95172-ce21-4778-ae54-6649149ee1fc), [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/ItoL2CompletionQuadVar`](https://prove2.me/theorems/6062fba0-aa8d-4423-8c5c-de5c7abb85aa), [`LevyStochCalc/Brownian/ItoL2CompletionApi`](https://prove2.me/theorems/2726bba3-f240-429d-9052-e494c979e1f0).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2Completion.lean) · `LevyStochCalc.Brownian.ItoL2Completion` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2Completion.lean#L1-L43 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Brownian.ItoL2Completion`, import-context bundle `KLSModular_LevyStochCalc_Brownian_ItoL2Completion`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2Completion.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2Completion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


