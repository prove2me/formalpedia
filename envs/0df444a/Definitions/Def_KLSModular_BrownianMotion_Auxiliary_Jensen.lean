-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Jensen
-- name    : KLSModular_BrownianMotion_Auxiliary_Jensen
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:43:55.836958+00:00
-- url     : https://prove2.me/theorems/64bc905d-b33c-4e61-a626-8eccc1cf8d1f
-- title:
--   Import context: BrownianMotion/Auxiliary/Jensen
-- statement:
--   This bundle retains the import context of the source module `BrownianMotion.Auxiliary.Jensen` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `BrownianMotion.Auxiliary.Analysis` and `BrownianMotion.Auxiliary.ENNReal`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen`, `Mathlib.MeasureTheory.Function.UniformIntegrable`, and `Mathlib.MeasureTheory.Function.ConditionalExpectation.Real`.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.Analysis
--   public import BrownianMotion.Auxiliary.ENNReal
--   public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
--   public import Mathlib.MeasureTheory.Function.UniformIntegrable
--   public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/Analysis`](https://prove2.me/theorems/6fa9ba03-daa8-46c1-b11b-1252e175fd7c), [`BrownianMotion/Auxiliary/ENNReal`](https://prove2.me/theorems/171cbd8b-7a32-47c8-8ad9-ffaf31ca7bf0).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Jensen.lean) · `BrownianMotion.Auxiliary.Jensen` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Jensen.lean#L1-L153 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `BrownianMotion.Auxiliary.Jensen`, import-context bundle `KLSModular_BrownianMotion_Auxiliary_Jensen`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0); upstream source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Jensen.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Analysis
import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_ENNReal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Jensen.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


