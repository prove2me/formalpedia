-- Prove2me | Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
-- name    : KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:01:44.535824+00:00
-- url     : https://prove2.me/theorems/ad3a4fc5-0540-409d-9b36-2eb87e3a6723
-- title:
--   Running maximum auxiliary definition
-- statement:
--   Vendored from the formal-mathfin library (https://github.com/raphaelrrcoelho/formal-mathfin). The private definition `MeasureTheory.runMax` assigns to a real-valued discrete-time process $f$, an index $n$, and an outcome $\omega$ the finite supremum of $f(k,\omega)$ over $k\in\{0,\ldots,n\}$. The uploaded declarations contain this auxiliary definition only; the module text does not provide the stated $L^p$ maximal-inequality theorem.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L57-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, definition bundle `KLS408915f_MathFin_Foundations_DoobLpMaximalInequality`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
namespace MeasureTheory
variable {Ω : Type*}
/-- Internal abbreviation for the running maximum
`max {f 0 ω, f 1 ω, …, f n ω}`. Kept `private`: the theorem
states the bound in terms of the explicit `Finset.sup'` form to match
`MeasureTheory.maximal_ineq`. -/
 def runMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ f k ω)
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}
end MeasureTheory


