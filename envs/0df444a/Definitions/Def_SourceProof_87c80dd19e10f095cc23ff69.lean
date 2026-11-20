-- Prove2me | Definitions.Def_SourceProof_87c80dd19e10f095cc23ff69
-- name    : SourceProof_87c80dd19e10f095cc23ff69
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:52:48.624859+00:00
-- url     : https://prove2.me/theorems/e6f0775a-4e10-4c79-a725-e4401c452d35
-- title:
--   LevyStochCalc source module: SourceProof_87c80dd19e10f095cc23ff69
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_ae_tendsto_per_param` comes from the `LevyStochCalc.Poisson.CompensatedDensityShifted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F000
import Definitions.Def_SourceProof_1e6256252a8bd3d3b339a9d9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The adapted (left-shifted) dyadic eval

The variant of the dyadic evaluation whose coefficient on the `i`-th dyadic interval is the
average of `φ` over the *previous* interval, hence `ℱ_{tᵢ}`-measurable for progressively
measurable `φ`. Its almost-everywhere and `L²(P ⊗ ds ⊗ ν)` convergence to `φ` follow from the
same Lebesgue-density and dominated-convergence arguments, the left shift contributing a
vanishing displacement.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Adapted (left-shifted) eval

The coefficient on the `i`-th dyadic interval is the average over the *previous*
interval (`dyadicAvg_shifted`), making it `ℱ_{tᵢ}`-measurable for progressively
measurable `φ` — the predictable/adapted version of `dyadicEval`. -/


theorem _root_.Prove2MeSourceProof.h_87c80dd19e10f095cc23ff69
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => dyadicEvalShifted T φ n s ω e) Filter.atTop (nhds (φ ω s e)) := by
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h_loc : MeasureTheory.LocallyIntegrable (fun s : ℝ => φ ω s e) volume :=
    LevyStochCalc.Poisson.Compensated.bounded_locallyIntegrable _ h_meas_slice M (fun s => hM ω s e)
  have h_leb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) h_loc 3
  have h_leb_r : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto (fun j => ⨍ y in Metric.closedBall (w j) (δ j), φ ω y e ∂volume)
          l (nhds (φ ω x e)) :=
    MeasureTheory.ae_restrict_of_ae h_leb
  have h_pos_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)), x ≠ 0 := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
    rw [this, Real.volume_singleton]
  filter_upwards [h_leb_r, h_pos_ae, MeasureTheory.ae_restrict_mem measurableSet_Icc]
    with x h_leb_x hx_ne hx_mem
  have hx : 0 < x ∧ x ≤ T := ⟨lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne), hx_mem.2⟩
  have hjlt : ∀ n, (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).val - 1 < 2 ^ n := fun n => by
    have := (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).isLt; omega
  set jp : (n : ℕ) → Fin (2 ^ n) :=
    fun n => ⟨(LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).val - 1, hjlt n⟩ with hjp
  set w : ℕ → ℝ := fun n =>
    (LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).castSucc + LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).succ) / 2 with hw
  set δ : ℕ → ℝ := fun n =>
    (LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).succ - LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).castSucc) / 2 with hδ
  have hδ_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n; rw [hδ]
    change (LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).succ - LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).castSucc) / 2 = _
    rw [LevyStochCalc.Poisson.Compensated.dyadicPartition_diff]; ring
  have hδ_pos : ∀ n, 0 < δ n := fun n => by rw [hδ_eq]; positivity
  have hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
      exact this.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr (fun n => by ring)
    exact (Filter.Tendsto.div_atTop tendsto_const_nhds h2pow).congr (fun n => (hδ_eq n).symm)
  have hδ_nhds : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ0, Filter.Eventually.of_forall hδ_pos⟩
  -- eventually the index is ≥ 1.
  have hev1 : ∀ᶠ n in Filter.atTop, 1 ≤ (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).val := by
    have hpow : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
    filter_upwards [hpow.eventually_gt_atTop (T / x)] with n hn
    have h1 : (1 : ℝ) < x * (2 ^ n : ℕ) / T := by
      rw [lt_div_iff₀ hT, one_mul]
      have h2 : T < (2 ^ n : ℕ) * x := (div_lt_iff₀ hx.1).mp hn
      linarith [h2]
    have hc : 1 < ⌈x * (2 ^ n : ℕ) / T⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast h1)
    simp only [LevyStochCalc.Poisson.Compensated.dyadicIndex]; omega
  -- x is within 3δ of the previous interval's centre, in symbolic `a, b` form.
  have hxball : ∀ᶠ n in Filter.atTop, x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [hev1] with n hn1
    set a := LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).castSucc with ha
    set b := LevyStochCalc.Poisson.Compensated.dyadicPartition T n (jp n).succ with hb
    have hval : ((LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc : ℕ) = ((jp n).succ : ℕ) := by
      simp only [hjp, Fin.val_castSucc, Fin.val_succ]; omega
    have hib : LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc = b := by
      rw [hb]; exact LevyStochCalc.Poisson.Compensated.dyadicPartition_val_congr hval
    have hba : a ≤ b := (LevyStochCalc.Poisson.Compensated.dyadicPartition_strictMono hT n).monotone Fin.castSucc_lt_succ.le
    have hdiff_j : b - a = T / (2 ^ n : ℕ) := LevyStochCalc.Poisson.Compensated.dyadicPartition_diff n (jp n)
    have hdiff_i : LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ
        - LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc = T / (2 ^ n : ℕ) :=
      LevyStochCalc.Poisson.Compensated.dyadicPartition_diff n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx)
    have hlo : b < x := by
      rw [← hib]; unfold LevyStochCalc.Poisson.Compensated.dyadicPartition; rw [Fin.val_castSucc]
      exact (_root_.Prove2MeSourceProof.h_e15e3b0d44b9d0242ba7b234 n T hT x hx).1
    have hx_hi_part : x ≤ LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ := by
      have h2 := (_root_.Prove2MeSourceProof.h_e15e3b0d44b9d0242ba7b234 n T hT x hx).2
      unfold LevyStochCalc.Poisson.Compensated.dyadicPartition; rw [Fin.val_succ]; push_cast at h2 ⊢; linarith [h2]
    rw [hib] at hdiff_i
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |x - (a + b) / 2| ≤ 3 * ((b - a) / 2)
    rw [abs_le]
    constructor <;> linarith [hlo, hx_hi_part, hdiff_i, hdiff_j, hba]
  -- bridge: shifted eval = closed-ball average centred at `wₙ` (definitional).
  have hbridge : ∀ᶠ n in Filter.atTop,
      LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n x ω e = ⨍ y in Metric.closedBall (w n) (δ n), φ ω y e ∂volume := by
    filter_upwards [hev1] with n hn1
    have hival : (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).val ≠ 0 := by omega
    rw [LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_eq_at_index hT φ n x hx ω e, LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted, dif_neg hival]
    change LevyStochCalc.Poisson.Compensated.dyadicAvg T φ n (jp n) ω e = _
    rw [_root_.Prove2MeSourceProof.h_1e6256252a8bd3d3b339a9d9 hT φ n (jp n) ω e]
  exact Filter.Tendsto.congr' (hbridge.mono (fun n h => h.symm)) (h_leb_x w δ hδ_nhds hxball)
end LevyStochCalc.Poisson.Compensated


