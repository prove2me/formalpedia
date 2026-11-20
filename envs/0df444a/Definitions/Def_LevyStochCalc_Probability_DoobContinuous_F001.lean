-- Prove2me | Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F001
-- name    : LevyStochCalc_Probability_DoobContinuous_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:03:07.946825+00:00
-- url     : https://prove2.me/theorems/a1590d5a-f68b-4389-9fca-b6dccb296e15
-- title:
--   Source declarations: LevyStochCalc.Probability.DoobContinuous
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.DoobContinuous. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F000
import Definitions.Def_SourceProof_d00ab70a6365c7b4a03cc45a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

/-! ### The dyadic partition of `[0, T]` -/

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-- Refining the level can only increase the sampled running maximum. -/
theorem enorm_dyadicRunMax_mono (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    Monotone fun n => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a, _root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
  refine iSup_le fun k => ?_
  refine le_iSup_of_le ⟨2 * (k : ℕ), ?_⟩ (le_of_eq ?_)
  · have hk : (k : ℕ) ≤ 2 ^ n := Nat.lt_succ_iff.mp k.isLt
    calc 2 * (k : ℕ) ≤ 2 * 2 ^ n := by omega
      _ < 2 ^ (n + 1) + 1 := by rw [pow_succ]; omega
  · rw [dyadicTime_succ_two_mul]
/-- Each sampled running maximum is measurable when the sampled slices are. -/
theorem measurable_enorm_dyadicRunMax (hM : ∀ t : ℝ, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  have heq : (fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞))
      = fun ω => ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) :=
    funext fun ω => _root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a M T n ω
  rw [heq]
  exact Measurable.iSup fun k =>
    ENNReal.continuous_coe.measurable.comp (hM (dyadicTime T n (k : ℕ))).nnnorm
/-! ### The supremum over the window -/

/-- The dyadic index whose partition point is the first at or after `t`. -/
noncomputable def dyadicIndex (T t : ℝ) (n : ℕ) : ℕ := ⌈t * 2 ^ n / T⌉₊
theorem dyadicIndex_le {T t : ℝ} (hT : 0 < T) (ht : t ≤ T) (n : ℕ) :
    dyadicIndex T t n ≤ 2 ^ n := by
  refine Nat.ceil_le.mpr ?_
  rw [div_le_iff₀ hT]
  push_cast
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
theorem le_dyadicTime_dyadicIndex {T t : ℝ} (hT : 0 < T) (htT : t ≤ T) (n : ℕ) :
    t ≤ dyadicTime T n (dyadicIndex T t n) := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hceil : t * 2 ^ n / T ≤ (dyadicIndex T t n : ℝ) := Nat.le_ceil _
  have h1 : t * 2 ^ n ≤ (dyadicIndex T t n : ℝ) * T := (div_le_iff₀ hT).mp hceil
  have hmul : t ≤ (dyadicIndex T t n : ℝ) * T / 2 ^ n := (le_div_iff₀ hpow).mpr h1
  exact le_min hmul htT
theorem dyadicTime_dyadicIndex_le_add {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (n : ℕ) :
    dyadicTime T n (dyadicIndex T t n) ≤ t + T / 2 ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hlt : (dyadicIndex T t n : ℝ) < t * 2 ^ n / T + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine le_trans (min_le_left _ _) ?_
  rw [div_le_iff₀ hpow]
  have hexp : (t + T / 2 ^ n) * 2 ^ n = t * 2 ^ n + T := by field_simp
  rw [hexp]
  have : (dyadicIndex T t n : ℝ) * T ≤ (t * 2 ^ n / T + 1) * T :=
    mul_le_mul_of_nonneg_right hlt.le hT.le
  calc (dyadicIndex T t n : ℝ) * T ≤ (t * 2 ^ n / T + 1) * T := this
    _ = t * 2 ^ n + T := by field_simp
/-- The dyadic points chosen by `dyadicIndex` approach `t` from the right. -/
theorem tendsto_dyadicTime_dyadicIndex {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    Filter.Tendsto (fun n => dyadicTime T n (dyadicIndex T t n)) Filter.atTop
      (nhdsWithin t (Set.Ici t)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Filter.Eventually.of_forall fun n => le_dyadicTime_dyadicIndex hT htT n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => t) (h := fun n => t + T / 2 ^ n) tendsto_const_nhds ?_
    (fun n => le_dyadicTime_dyadicIndex hT htT n)
    (fun n => dyadicTime_dyadicIndex_le_add hT ht n)
  have hhalf : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd : ∀ n : ℕ, T / 2 ^ n = T * ((1 : ℝ) / 2) ^ n := fun n => by
    rw [div_pow, one_pow]
    ring
  have htend0 : Filter.Tendsto (fun n : ℕ => T / 2 ^ n) Filter.atTop (nhds 0) := by
    simp only [hd]
    simpa using hhalf.const_mul T
  simpa using tendsto_const_nhds.add htend0
/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/

end LevyStochCalc.Probability


