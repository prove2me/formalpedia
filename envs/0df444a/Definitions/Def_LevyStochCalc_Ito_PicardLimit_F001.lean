-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardLimit_F001
-- name    : LevyStochCalc_Ito_PicardLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:38:46.358914+00:00
-- url     : https://prove2.me/theorems/7e27a54a-2a8c-48b3-8ce9-99d8e6006789
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLimit_F000
import Definitions.Def_SourceProof_f2a84f529af8c217678c06c1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of Bielecki-Cauchy sequences of path maps

A sequence of path maps whose consecutive Bielecki differences are summable converges: at every
time of the window the increments are summable in `L²`, hence almost surely absolutely summable,
so the pointwise `limsup` is the almost-sure limit. The `limsup` inherits joint measurability and
progressive measurability from the sequence, and the Bielecki distance to the sequence tends to
zero.

The Bielecki norm is the weighted supremum over `t` of the `L²` norms, so it controls the paths
at each fixed time only: a càdlàg property of the terms is not inherited by the limit. The limit
constructed here is therefore a jointly measurable, progressively measurable path map, not an
`SBoundedProcess`; the càdlàg property of a Picard fixed point comes from the Picard step's own
output, not from the limit.

## Main statements

* `bieleckiLimit` — the pointwise `limsup` of a sequence of path maps.
* `measurable_bieleckiLimit`, `progressivelyMeasurable_bieleckiLimit` — its measurability.
* `bieleckiNorm_le_of_perTime_rpow`, `lintegral_sq_rpow_le_of_bieleckiNorm` — the two directions
  between the Bielecki norm and the weighted `L²` norms at a fixed time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The Bielecki norm and the weighted `L²` norms at a fixed time -/

/-! ### The limit path map -/

/-! ### Telescoping -/

/-! ### Almost sure convergence at a fixed time -/

/-! ### Convergence to the limit path map -/

/-- **The Bielecki limit.** A sequence of jointly measurable path maps whose consecutive Bielecki
differences are summable converges in Bielecki norm to `bieleckiLimit X`, at the rate given by the
tail of the step bounds. -/
theorem bieleckiNorm_sub_bieleckiLimit_le (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i) ≤ c k)
    (hc : ∑' k, c k ≠ ⊤) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i => X k t ω i - bieleckiLimit X t ω i)
      ≤ ∑' j, c (k + j) :=
  bieleckiNorm_le_of_perTime_rpow (P := P) β T _ _ fun _t ht =>
    _root_.Prove2MeSourceProof.h_f2a84f529af8c217678c06c1 (P := P) β T hmeas hstep hc k ht
/-! ### The geometric case -/

/-- The tail of a geometric series of `ℝ≥0∞` step bounds. -/
theorem tsum_geometric_shift {q C : ℝ≥0∞} (k : ℕ) :
    ∑' j, q ^ (k + j) * C = q ^ k * ((1 - q)⁻¹ * C) := by
  calc ∑' j, q ^ (k + j) * C = ∑' j, q ^ k * (q ^ j * C) := by
        refine tsum_congr fun j => ?_
        rw [pow_add, mul_assoc]
    _ = q ^ k * ∑' j, q ^ j * C := ENNReal.tsum_mul_left
    _ = q ^ k * ((1 - q)⁻¹ * C) := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
/-- **The Bielecki limit of a geometrically Cauchy sequence.** If the consecutive Bielecki
differences decay geometrically at a rate `< 1`, the sequence converges to `bieleckiLimit` at that
rate. -/
theorem bieleckiNorm_sub_bieleckiLimit_geometric (β T : ℝ) {X : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hmeas : ∀ k, Measurable (Function.uncurry (X k))) {q C : ℝ≥0∞}
    (hstep : ∀ k, bieleckiNorm (P := P) β T (fun t ω i => X (k + 1) t ω i - X k t ω i)
      ≤ q ^ k * C) (hq : q < 1) (hC : C ≠ ⊤) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i => X k t ω i - bieleckiLimit X t ω i)
      ≤ q ^ k * ((1 - q)⁻¹ * C) := by
  have hsub : (1 : ℝ≥0∞) - q ≠ 0 := (tsub_pos_of_lt hq).ne'
  have hc : ∑' k, q ^ k * C ≠ ⊤ := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hsub) hC
  refine le_trans (bieleckiNorm_sub_bieleckiLimit_le (P := P) β T hmeas hstep hc k)
    (le_of_eq (tsum_geometric_shift k))
end LevyStochCalc.Ito.Picard


