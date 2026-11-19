-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F000
-- name    : LevyStochCalc_Brownian_ContinuityDyadicChaining_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:11:17.628243+00:00
-- url     : https://prove2.me/theorems/06cef756-f17d-478c-a354-407844db704b
-- title:
--   Source declarations: LevyStochCalc.Brownian.ContinuityDyadicChaining
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ContinuityDyadicChaining. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Construction_F000
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic chaining for the Kolmogorov-Chentsov theorem

The deterministic half of the Kolmogorov-Chentsov construction. A function that is
`α`-Hölder on a dense set `D ⊆ ℝ` at scales `≤ δ₀` is uniformly continuous on `D` and so
extends continuously to `ℝ`; the dyadic rationals `{k · 2^(-n) : k ∈ ℤ, n ∈ ℕ}` are such a
dense set, and the level-`n` dyadic truncation `⌊x · 2^n⌋ / 2^n` approximates each real from
below. Chaining these truncations turns a bound `b n` on the consecutive level-`n` dyadic
increments of `f` into `α`-Hölder continuity of `f` on the dyadics of `[0, 1)`
(`dyadic_holder_chaining`), for `b n = C · 2^(-α n)`.

No probability enters here; the random increment bounds are supplied in
`LevyStochCalc.Brownian.ContinuityKolmogorovBounds`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

/-- The set of dyadic rationals: `D := {k * 2^{-n} : k ∈ ℤ, n ∈ ℕ}`. Dense in ℝ. -/
def dyadicRationals : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) * (2 : ℝ)^(-n : ℤ)}
/-- `0` is a dyadic rational (`k = 0`, `n = 0`). -/
lemma zero_mem_dyadicRationals : (0 : ℝ) ∈ dyadicRationals := by
  refine ⟨0, 0, ?_⟩
  simp
/-- Every integer is a dyadic rational (`n = 0`). -/
lemma intCast_mem_dyadicRationals (k : ℤ) : (k : ℝ) ∈ dyadicRationals := by
  refine ⟨k, 0, ?_⟩
  simp
/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/

end LevyStochCalc.Brownian.Continuity


