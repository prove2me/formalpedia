-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharlierGenerating_F000
-- name    : LevyStochCalc_Probability_CharlierGenerating_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:13:50.916686+00:00
-- url     : https://prove2.me/theorems/ccfecba9-b6ee-4cc9-8b3a-3c3cdc759aec
-- title:
--   Source declarations: LevyStochCalc.Probability.CharlierGenerating
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CharlierGenerating. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Charlier_F001
import Definitions.Def_LevyStochCalc_Probability_Charlier_F002
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Charlier polynomials

At a natural argument `n` the Charlier polynomials with parameter `lam` (the mean of the Poisson
law that makes them orthogonal) are generated over `ℂ` by
`e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)`, obtained by induction on `n`: the value
`C_s(0; lam) = (-lam) ^ s` matches the exponential series at `n = 0`, and the forward difference
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)` turns the step into an index shift, which on the
generating side multiplies by `1 + t`. The same induction, run on the bound
`|T_(s+1)(n + 1)| ≤ |T_(s+1)(n)| + |t| |T_s(n)|` for the terms `T_s(n) = (t ^ s / s!) C_s(n; lam)`
and started from the exponential series at `n = 0`, shows that the series is absolutely summable
at every natural argument.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_zero_arg` — `C_s(0; lam) = (-lam) ^ s`.
* `LevyStochCalc.Probability.hasSum_charlierScaled` —
  `e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_charlierScaled` — absolute summability of
  `t ^ s / s! · C_s(n; lam)` at every natural argument.
-/

namespace LevyStochCalc.Probability

open Finset

/-- `C_s(0; lam) = (-lam)^s`. -/
theorem charlierScaled_zero_arg (lam : ℝ) (s : ℕ) :
    charlierScaled s lam 0 = (-lam) ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [charlierScaled_succ, ih]; ring
/-- The successor shift is injective on the naturals. -/
private theorem add_one_injective : Function.Injective (fun s : ℕ => s + 1) := fun a b h => by
  simpa using h
end LevyStochCalc.Probability


