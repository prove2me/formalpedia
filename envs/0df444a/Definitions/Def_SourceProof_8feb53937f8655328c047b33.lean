-- Prove2me | Definitions.Def_SourceProof_8feb53937f8655328c047b33
-- name    : SourceProof_8feb53937f8655328c047b33
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:51:35.975084+00:00
-- url     : https://prove2.me/theorems/0fc9c8f1-7fd8-469f-b4e6-fc3580bb744b
-- title:
--   LevyStochCalc source module: SourceProof_8feb53937f8655328c047b33
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.predictable_pointwise_tendsto_per_omega` comes from the `LevyStochCalc.Brownian.ItoDensityPointwise` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001
import Definitions.Def_SourceProof_002a923f0aea54a69dd78500
import Definitions.Def_SourceProof_02c37e83f498df3491d7f8c9
import Definitions.Def_SourceProof_fb9bb6c8d4545e37b51e590f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere convergence of the dyadic averages

Lebesgue differentiation for a bounded jointly measurable integrand: the dyadic cell
averages, shifted and unshifted, converge to the integrand at almost every point of
`Ω × [0,T]`, and for the unshifted family the convergence also holds in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_8feb53937f8655328c047b33
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- K = 3 Vitali on g(ω, ·).
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    _root_.Prove2MeSourceProof.h_02c37e83f498df3491d7f8c9 (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  have h_vitali_K3 := IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 3
  have h_vitali_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l
            (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_vitali_K3
  -- Exclude {0}.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_vitali_restrict
  filter_upwards [h_vitali_restrict, h_pos_ae] with x h_vitali_at_x hx_ne_zero hx_mem
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Half-width δ_n = T/2^{n+1}.
  set δ : ℕ → ℝ := fun n => T / (2 * (2 ^ n : ℕ)) with hδ_def
  -- Center w_n = (i - 1/2) * T/2^n.  For i ≥ 1, this is the midpoint of (t_{i-1}, t_i].
  -- For i = 0 (which is eventually false), this is a dummy value.
  set w : ℕ → ℝ := fun n =>
    (((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
    with hw_def
  -- δ → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := fun n => by
    change 0 < T / (2 * (2 ^ n : ℕ))
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- Eventually 0 < (dyadicIndex n s).val (i.e., for n large, i ≥ 1).
  have h_eventually_i_pos :
      ∀ᶠ n in Filter.atTop, 0 < (LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val := by
    -- For n large enough, T/2^n < x → t_1 ≤ x → i ≥ 1.
    have h_pow_to_inf : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
      exact tendsto_natCast_atTop_iff.mpr this
    have h_T_div_pow : Filter.Tendsto (fun n : ℕ => T / ((2 ^ n : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h_pow_to_inf
    have h_evnt : ∀ᶠ n in Filter.atTop, T / ((2 ^ n : ℕ) : ℝ) < x := by
      have := h_T_div_pow.eventually_lt_const hx_strict_pos
      exact this
    filter_upwards [h_evnt] with n hn
    -- (dyadicIndex n T hT x hx).val > 0: from dyadicIndex_mem, t_i < x ≤ t_{i+1}.
    -- If i.val = 0, then t_i = 0 and t_{i+1} = T/2^n. Since t_{i+1} ≥ x means
    -- T/2^n ≥ x, contradicting hn.
    by_contra h_not_pos
    push Not at h_not_pos
    have h_i_zero : (LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val = 0 := Nat.eq_zero_of_le_zero h_not_pos
    have hi_mem := _root_.Prove2MeSourceProof.h_d2dcdd70ae2c689ce98c5bad n T hT x hx
    have h_x_le : x ≤ T / ((2 ^ n : ℕ) : ℝ) := by
      have := hi_mem.2
      simp only [h_i_zero, Nat.cast_zero, zero_add, one_mul] at this
      exact this
    linarith
  -- For n with i ≥ 1, x ∈ closedBall(w_n, 3 δ_n).
  have h_x_in_ball_eventually : ∀ᶠ n in Filter.atTop,
      x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    change |x - w n| ≤ 3 * δ n
    have hi_mem := _root_.Prove2MeSourceProof.h_d2dcdd70ae2c689ce98c5bad n T hT x hx
    have h_x_lower : ((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) * T / ((2 ^ n : ℕ) : ℝ) < x :=
      hi_mem.1
    have h_x_upper :
        x ≤ (((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) + 1) * T / ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hi_mem.2
    set i_val : ℝ := ((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) with hi_val
    have h_pos_real : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos_real
    change |x - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))| ≤ 3 * (T / (2 * (2 ^ n : ℕ)))
    rw [abs_le]
    constructor
    · -- Lower bound: x - w_n ≥ -(3 * δ_n).
      have h_x_lower' : i_val * T / ((2 ^ n : ℕ) : ℝ) ≤ x := le_of_lt h_x_lower
      have h_alg : i_val * T / ((2 ^ n : ℕ) : ℝ) - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ)) =
          T / (2 * ((2 ^ n : ℕ) : ℝ)) := by
        field_simp; ring
      have h_3delta_pos : 0 < 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by positivity
      linarith
    · -- Upper: x - w_n ≤ 3 δ_n.
      have h_alg :
          (i_val + 1) * T / ((2 ^ n : ℕ) : ℝ)
            - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
            = 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by
        field_simp; ring
      linarith
  -- Apply Vitali theorem.
  have h_avg_to_g := h_vitali_at_x hx_mem (l := Filter.atTop) w δ
    h_delta_tendsto h_x_in_ball_eventually
  -- Bridge: ⨍ over closedBall = predictable.eval (eventually).
  have h_bridge : ∀ᶠ n in Filter.atTop,
      (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    rw [_root_.Prove2MeSourceProof.h_002a923f0aea54a69dd78500 hT g h_meas M h_bound n x hx ω]
    -- dyadicAvg_shifted T g n i ω = dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω (since i ≥ 1)
    -- = ⨍ over closedBall(midpt of (t_{i-1}, t_i], T/2^{n+1}) g(ω, ·)
    unfold LevyStochCalc.Brownian.Ito.dyadicAvg_shifted_brownian
    rw [dif_neg (by omega : ¬ (dyadicIndex n T hT x hx).val = 0)]
    have h_lt : (LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val - 1 < 2 ^ n := by
      have := (LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).isLt; omega
    set i' : Fin (2 ^ n) := ⟨(LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val - 1, h_lt⟩
    rw [_root_.Prove2MeSourceProof.h_fb9bb6c8d4545e37b51e590f hT g n i' ω]
    -- Now match w_n and δ_n with the closedBall arguments.
    have h_w_eq : w n =
        (LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i'.castSucc +
          LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i'.succ) / 2 := by
      change (((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) - 1/2) *
          (T / ((2 ^ n : ℕ) : ℝ)) = _
      unfold LevyStochCalc.Brownian.Ito.dyadicPartition_brownian
      simp only [Fin.val_succ, Fin.val_castSucc]
      have h_pow_pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
      have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
      have h_sub_cast :
          (((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val - 1 : ℕ) : ℝ) =
            ((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (dyadicIndex n T hT x hx).val)]
        simp
      rw [h_sub_cast]
      have h_add_one_cast :
          ((((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 : ℕ) : ℝ) =
            ((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val : ℝ) := by
        rw [show ((LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 = (LevyStochCalc.Brownian.Ito.dyadicIndex n T hT x hx).val from
          by omega]
      rw [h_add_one_cast]
      field_simp
      ring
    have h_delta_eq : δ n = (LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i'.succ -
        LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i'.castSucc) / 2 := by
      rw [LevyStochCalc.Brownian.Ito.dyadicPartition_brownian_diff n i']
      change T / (2 * ((2 ^ n : ℕ) : ℝ)) = T / ((2 ^ n : ℕ) : ℝ) / 2
      field_simp
    rw [h_w_eq, h_delta_eq]
  refine Filter.Tendsto.congr' ?_ h_avg_to_g
  filter_upwards [h_bridge] with n hn
  exact hn.symm
end LevyStochCalc.Brownian.Ito


