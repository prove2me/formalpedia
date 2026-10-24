-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
-- name    : KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:15:56.439644+00:00
-- url     : https://prove2.me/theorems/04857271-d5a6-4249-b540-2f47ab044c61
-- title:
--   Dyadic rationals and dyadic truncation
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The set `dyadicRationals` consists of real numbers of the form k · 2^(−n), with k ∈ ℤ and n ∈ ℕ. The noncomputable function `dyadicTrunc` maps x ∈ ℝ to floor(x · 2ⁿ) divided by 2ⁿ, the level-n dyadic approximation from below. This bundle contains these definitions only; the surrounding module documents their use in deterministic Hölder chaining.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L103-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, definition bundle `KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace LevyStochCalc
namespace Brownian
namespace Continuity
/-- The set of dyadic rationals: `D := {k * 2^{-n} : k ∈ ℤ, n ∈ ℕ}`. Dense in ℝ. -/
def dyadicRationals : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) * (2 : ℝ)^(-n : ℤ)}
/-- Level-`n` dyadic truncation `⌊x·2ⁿ⌋ / 2ⁿ` — the largest level-`n` dyadic
`≤ x`. -/
noncomputable def dyadicTrunc (n : ℕ) (x : ℝ) : ℝ := (⌊x * 2 ^ n⌋ : ℝ) / 2 ^ n
end Continuity
end Brownian
end LevyStochCalc


