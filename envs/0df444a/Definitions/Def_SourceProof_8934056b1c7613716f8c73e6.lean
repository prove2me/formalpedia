-- Prove2me | Definitions.Def_SourceProof_8934056b1c7613716f8c73e6
-- name    : SourceProof_8934056b1c7613716f8c73e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:10:34.894021+00:00
-- url     : https://prove2.me/theorems/86bddfc2-1e85-4f9a-9018-c720a4a7f893
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Continuity.kc_exponent_identity
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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

/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/


theorem _root_.Prove2MeSourceProof.h_8934056b1c7613716f8c73e6 {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  have e1 : ((1 / 2 : ℝ) ^ n) ^ q = (1 / 2 : ℝ) ^ ((n : ℝ) * q) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) n, ← Real.rpow_mul (le_of_lt h2)]
  have e2 : (((1 / 2 : ℝ) ^ α) ^ n) ^ p = (1 / 2 : ℝ) ^ (α * (n : ℝ) * p) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) n, ← Real.rpow_mul (le_of_lt h2),
        ← Real.rpow_mul (le_of_lt h2)]
  have e3 : (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt h2), Real.rpow_natCast,
        show (1 / 2 : ℝ) ^ n = (2 ^ n)⁻¹ from by rw [one_div, inv_pow], inv_inv]
  have e4 : ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n
      = (1 / 2 : ℝ) ^ ((q - α * p - 1) * (n : ℝ)) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (q - α * p - 1)) n,
        ← Real.rpow_mul (le_of_lt h2)]
  rw [e1, e2, e3, e4, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt h2),
      ← Real.rpow_add h2, ← Real.rpow_add h2]
  congr 1
  ring
end LevyStochCalc.Brownian.Continuity


