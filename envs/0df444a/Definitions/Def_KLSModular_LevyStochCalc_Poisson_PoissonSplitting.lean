-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_PoissonSplitting
-- name    : KLSModular_LevyStochCalc_Poisson_PoissonSplitting
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:40:49.032024+00:00
-- url     : https://prove2.me/theorems/66e06598-17d9-4f53-9059-6ebb3b15c3b4
-- title:
--   Import context: LevyStochCalc/Poisson/PoissonSplitting
-- statement:
--   This bundle retains the import context of the source module `LevyStochCalc.Poisson.PoissonSplitting` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Probability.Distributions.Poisson.Basic`, `Mathlib.Probability.Independence.Integration`, `Mathlib.Probability.Independence.InfinitePi`, and `Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Probability.Distributions.Poisson.Basic
--   import Mathlib.Probability.Independence.Integration
--   import Mathlib.Probability.Independence.InfinitePi
--   import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/PoissonSplitting.lean) · `LevyStochCalc.Poisson.PoissonSplitting` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/PoissonSplitting.lean#L1-L427 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `LevyStochCalc.Poisson.PoissonSplitting`, import-context bundle `KLSModular_LevyStochCalc_Poisson_PoissonSplitting`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0); upstream source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/PoissonSplitting.lean. Original vendor notices are retained in the generated Lean text.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/PoissonSplitting.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


