-- Prove2me | Definitions.Def_SourceProof_41999f352e28c058ae5e27f5
-- name    : SourceProof_41999f352e28c058ae5e27f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:58:45.517691+00:00
-- url     : https://prove2.me/theorems/0159fe68-e191-4eb1-9507-b6e1b445e645
-- title:
--   LevyStochCalc source module: SourceProof_41999f352e28c058ae5e27f5
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.dyadicEval_ae_tendsto_per_param` comes from the `LevyStochCalc.Poisson.CompensatedDensityDyadic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F002
import Definitions.Def_SourceProof_1e6256252a8bd3d3b339a9d9

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic time-discretisation of a mark-dependent integrand

The dyadic partition `tᵢ = i·T/2ⁿ` of `[0,T]`, the interval time-averages of a bounded
integrand `φ : Ω → ℝ → E → ℝ` with the mark carried as a parameter, and the piecewise-constant
evaluation `dyadicEval` built from them. For a bounded jointly measurable `φ`, the Lebesgue
density theorem gives almost-everywhere convergence of `dyadicEval` to `φ` in the time variable,
and dominated convergence upgrades it to convergence in `L²(P ⊗ ds ⊗ ν)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/


theorem _root_.Prove2MeSourceProof.h_41999f352e28c058ae5e27f5
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => dyadicEval T φ n s ω e) Filter.atTop (nhds (φ ω s e)) := by
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h_loc : MeasureTheory.LocallyIntegrable (fun s : ℝ => φ ω s e) volume :=
    LevyStochCalc.Poisson.Compensated.bounded_locallyIntegrable _ h_meas_slice M (fun s => hM ω s e)
  have h_leb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) h_loc 1
  have h_leb_r : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
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
  -- per-level dyadic interval endpoints of `x`.
  have hmem : ∀ n, LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc < x ∧
      x ≤ LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ := by
    intro n
    have h := _root_.Prove2MeSourceProof.h_e15e3b0d44b9d0242ba7b234 n T hT x hx
    have hpc : LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc
        = ((LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
      unfold LevyStochCalc.Poisson.Compensated.dyadicPartition; rw [Fin.val_castSucc]
    have hps : LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ
        = (((LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
      unfold LevyStochCalc.Poisson.Compensated.dyadicPartition; rw [Fin.val_succ]; push_cast; ring
    rw [hpc, hps]; exact h
  set w : ℕ → ℝ := fun n =>
    (LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc +
      LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ) / 2 with hw
  set δ : ℕ → ℝ := fun n =>
    (LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ -
      LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc) / 2 with hδ
  have hδ_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n
    change (LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).succ -
      LevyStochCalc.Poisson.Compensated.dyadicPartition T n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx).castSucc) / 2 = _
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
  have hxball : ∀ n, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    intro n
    rw [one_mul, Metric.mem_closedBall, Real.dist_eq]
    obtain ⟨h1, h2⟩ := hmem n
    rw [hw, hδ, abs_le]; constructor <;> simp only <;> linarith
  have h_avg := h_leb_x w δ hδ_nhds (Filter.Eventually.of_forall hxball)
  have h_bridge : ∀ n, LevyStochCalc.Poisson.Compensated.dyadicEval T φ n x ω e
      = ⨍ y in Metric.closedBall (w n) (δ n), φ ω y e ∂volume := by
    intro n
    rw [LevyStochCalc.Poisson.Compensated.dyadicEval_eq_dyadicAvg_at_index hT φ n x hx ω e,
      _root_.Prove2MeSourceProof.h_1e6256252a8bd3d3b339a9d9 hT φ n (LevyStochCalc.Poisson.Compensated.dyadicIndex n T hT x hx) ω e]
  simp_rw [h_bridge]; exact h_avg
end LevyStochCalc.Poisson.Compensated


