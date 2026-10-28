-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Basic
-- name    : KLSModular_LevyStochCalc_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:33:23.298593+00:00
-- url     : https://prove2.me/theorems/0adc36c3-8b48-4256-a1bd-556fe85cdbbb
-- title:
--   Import context: LevyStochCalc/Basic
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Basic` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Function.LpSeminorm.Basic`, `Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality`, `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.MeasureTheory.Measure.Prod`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`, `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`, `Mathlib.Analysis.SpecialFunctions.Pow.Continuity`, and `Mathlib.Topology.Order.MonotoneContinuity`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
--   import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
--   import Mathlib.MeasureTheory.Function.LpSpace.Basic
--   import Mathlib.MeasureTheory.Measure.Prod
--   import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
--   import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
--   import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
--   import Mathlib.Topology.Order.MonotoneContinuity
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Basic.lean) · `LevyStochCalc.Basic` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Basic.lean#L1-L420 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Basic`, import-context bundle `KLSModular_LevyStochCalc_Basic`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Basic.lean. Original vendor notices are retained in the generated Lean text.

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Basic.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


