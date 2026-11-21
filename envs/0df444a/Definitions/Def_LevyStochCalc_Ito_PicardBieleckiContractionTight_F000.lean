-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
-- name    : LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:04:16.810171+00:00
-- url     : https://prove2.me/theorems/c743eac2-8091-4796-8295-812407100877
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardBieleckiContractionTight
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardBieleckiContractionTight. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction at the literature-tight rate

The refinement of the Bielecki-norm contraction estimate that takes the diffusion and jump bounds
in their tight form, without the redundant time factor, giving the constant `3 n L² (T + 2)` in
place of `9 n L² T` and hence the contraction rate `3 n L² (T + 2) / (2β)`; together with the
threshold `3 n L² (T + 2) < 2β` under which that rate is `< 1`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Tight Picard contraction rate threshold.**

The tight Picard contraction rate `3 n L² (T + 2) / (2β)` is `< 1`
iff `β > 3 n L² (T + 2) / 2`.

This is the threshold condition for the Picard map to be a strict
contraction in the Bielecki β-norm under the tight rate. Pairing with
`picardStep_bielecki_contraction_tight` and the Bielecki weight bound
`bielecki_weighted_integral_bound`, the resulting estimate

  `e^{-2βt} · ‖Φ X t - Φ Y t‖_{L²(P)}²`
  `  ≤ (3 n L² (T + 2) / (2β)) · ‖X - Y‖_{β,T}²`

is a strict contraction for `β > 3 n L² (T + 2) / 2`.

For `T ≥ 1` and `n ≥ 1`, this threshold is strictly less than the
original loose threshold `9 n L² T / 2` (since `T + 2 ≤ 3 T` when
`T ≥ 1`), so the Picard fixed point exists at a smaller `β`. -/
lemma picardStep_bielecki_contraction_tight_rate_lt_one
    (n : ℕ) {L : ℝ} (_hL_nn : 0 ≤ L)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : 3 * (n : ℝ) * L ^ 2 * (T + 2) < 2 * β) :
    3 * (n : ℝ) * L ^ 2 * (T + 2) / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_T2_nn : 0 ≤ T + 2 := by linarith
    have h_LHS_nn : 0 ≤ 3 * (n : ℝ) * L ^ 2 * (T + 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (sq_nonneg L)) h_T2_nn
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold
end LevyStochCalc.Ito.Picard


