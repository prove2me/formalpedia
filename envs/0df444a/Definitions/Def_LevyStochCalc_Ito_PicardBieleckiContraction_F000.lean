-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000
-- name    : LevyStochCalc_Ito_PicardBieleckiContraction_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:44.820993+00:00
-- url     : https://prove2.me/theorems/9975178a-1052-4184-91db-9be3632c2dc9
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardBieleckiContraction
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardBieleckiContraction. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Bielecki-norm contraction estimate for the Picard map

At each time of the window the `L²` mass of the difference of two Picard steps is bounded by
`9 n L² T` times the doubly-integrated energy of the difference of their arguments, so that under
the Bielecki weight `e^{-2βt}` the map contracts at rate `9 n L² T / (2β)`; together with the
threshold `9 n L² T < 2β` under which that rate is `< 1`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Picard contraction rate threshold.**

The Picard contraction rate `9 n L² T / (2β)` is `< 1` iff `β > 9 n L² T / 2`.

This is the threshold condition for the Picard map to be a strict contraction
in the Bielecki β-norm. Pairing with `picardStep_bielecki_contraction` and
the Bielecki weight bound `bielecki_weighted_integral_bound`, the resulting
estimate

  `e^{-2βt} · ‖Φ X t - Φ Y t‖_{L²(P)}² ≤ (9 n L² T / (2β)) · ‖X - Y‖_{β,T}²`

is a strict contraction for `β > 9 n L² T / 2`. -/
lemma picardStep_bielecki_contraction_rate_lt_one
    (n : ℕ) {L : ℝ} (_hL_nn : 0 ≤ L)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : 9 * (n : ℝ) * L ^ 2 * T < 2 * β) :
    9 * (n : ℝ) * L ^ 2 * T / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_LHS_nn : 0 ≤ 9 * (n : ℝ) * L ^ 2 * T :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (sq_nonneg L)) hT_pos.le
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold
end LevyStochCalc.Ito.Picard


