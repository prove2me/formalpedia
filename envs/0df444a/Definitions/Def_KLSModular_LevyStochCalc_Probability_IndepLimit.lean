-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepLimit
-- name    : KLSModular_LevyStochCalc_Probability_IndepLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:40:30.753883+00:00
-- url     : https://prove2.me/theorems/ac0424d7-d764-4c8c-a864-a544a34482ff
-- title:
--   Import context: LevyStochCalc/Probability/IndepLimit
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Probability.IndepLimit` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Probability.Independence.Integration`, `Mathlib.MeasureTheory.Measure.HasOuterApproxClosed`, and `Mathlib.MeasureTheory.Integral.DominatedConvergence`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Probability.Independence.Integration
--   import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
--   import Mathlib.MeasureTheory.Integral.DominatedConvergence
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`setIntegral_eq_measure_mul_of_indep`](https://prove2.me/theorems/2e1bc799-70a4-40fd-9d3b-4b7628082683)
--   - [`indep_comap_of_tendsto_ae`](https://prove2.me/theorems/0db49de1-10a5-4abf-9357-4de5587f1381)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/IndepLimit.lean) · `LevyStochCalc.Probability.IndepLimit` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/IndepLimit.lean#L1-L99 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Probability.IndepLimit`, import-context bundle `KLSModular_LevyStochCalc_Probability_IndepLimit`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/IndepLimit.lean. Original vendor notices are retained in the generated Lean text.

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


