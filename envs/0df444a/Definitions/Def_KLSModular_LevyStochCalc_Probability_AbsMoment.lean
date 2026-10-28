-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment
-- name    : KLSModular_LevyStochCalc_Probability_AbsMoment
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:50:43.183953+00:00
-- url     : https://prove2.me/theorems/a47bc9f6-36f4-49ba-b8be-98961f4f3386
-- title:
--   Import context: LevyStochCalc/Probability/AbsMoment
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Probability.AbsMoment` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`, `Mathlib.Analysis.SpecialFunctions.Sqrt`, and `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Integral.Bochner.Basic
--   import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
--   import Mathlib.Analysis.SpecialFunctions.Sqrt
--   import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`integral_abs_le_sqrt_of_integral_sq_le`](https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149)
--   - [`integral_abs_add_four_le`](https://prove2.me/theorems/1d271bc2-3915-4ac6-a74e-692ff5624511)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/AbsMoment.lean) · `LevyStochCalc.Probability.AbsMoment` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/AbsMoment.lean#L1-L109 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Probability.AbsMoment`, import-context bundle `KLSModular_LevyStochCalc_Probability_AbsMoment`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/AbsMoment.lean. Original vendor notices are retained in the generated Lean text.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/AbsMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


