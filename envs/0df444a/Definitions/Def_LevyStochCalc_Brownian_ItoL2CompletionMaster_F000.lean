-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionMaster_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:07:55.559338+00:00
-- url     : https://prove2.me/theorems/8779be01-6f0b-4e7d-9e4d-b9ef7a1d2049
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionMaster
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionMaster. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F001
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F001
import Definitions.Def_SourceProof_3d4df4df753a663d9a385c25
import Definitions.Def_SourceProof_c5a0aac77ea3887770fece7e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- Positivity of the master horizon `(n : ℝ) + 1`. -/
lemma master_horizon_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
/-- Positivity of the master tolerance `((n : ℝ≥0∞) + 1)⁻¹`. -/
private lemma master_tol_pos (n : ℕ) : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
  ENNReal.inv_pos.mpr (by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
/-- **Master approximating sequence.** For each `n`, an adapted `SimplePredictable`
on horizon `(n : ℝ) + 1` within `((n : ℝ≥0∞) + 1)⁻¹` of `H` in `L²([0, n+1] × Ω)`.
The horizons grow to `∞`; zero-extension lets these be compared across `n`. -/
noncomputable def masterApprox (n : ℕ) : SimplePredictable Ω ((n : ℝ) + 1) :=
  (exists_adaptedSimple_within ℱ H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose
lemma masterApprox_adapt (n : ℕ) :
    ∀ i : Fin (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition i.castSucc))
        ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ i) :=
  (exists_adaptedSimple_within ℱ H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose_spec.1
lemma masterApprox_within (n : ℕ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1),
      (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ((n : ℝ≥0∞) + 1)⁻¹ :=
  (exists_adaptedSimple_within ℱ H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose_spec.2
include hℱ in
/-- **Cross-horizon difference isometry for the master sequence.** Extending both
`masterApprox n` and `masterApprox m` to the common horizon `max n m + 2` (via
`appendInterval`, which leaves their `simpleIntegral` and `eval` unchanged), the
difference isometry gives `∫⁻‖Iₙ(t) − Iₘ(t)‖² = ∫⁻∫⁻_{[0,t]}‖Gₙ.eval − Gₘ.eval‖²`
for every `t ≥ 0`. -/
lemma masterApprox_diff_isometry (n m : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
        - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω
            - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
  set Gn := masterApprox ℱ H h_meas h_progMeas h_sq_int_global n with hGn
  set Gm := masterApprox ℱ H h_meas h_progMeas h_sq_int_global m with hGm
  have hKn : Gn.partition (Fin.last Gn.N) < (max n m : ℝ) + 2 := by
    have h1 : Gn.partition (Fin.last Gn.N) ≤ (n : ℝ) + 1 := Gn.partition_le_T
    have h2 : (n : ℝ) ≤ (max n m : ℝ) := by exact_mod_cast Nat.le_max_left n m
    linarith
  have hKm : Gm.partition (Fin.last Gm.N) < (max n m : ℝ) + 2 := by
    have h1 : Gm.partition (Fin.last Gm.N) ≤ (m : ℝ) + 1 := Gm.partition_le_T
    have h2 : (m : ℝ) ≤ (max n m : ℝ) := by exact_mod_cast Nat.le_max_right n m
    linarith
  have h_eq : (Gn.appendInterval hKn).partition (Fin.last (Gn.appendInterval hKn).N)
      = (Gm.appendInterval hKm).partition (Fin.last (Gm.appendInterval hKm).N) :=
    (Gn.appendInterval_partition_last hKn).trans (Gm.appendInterval_partition_last hKm).symm
  have ha_n := Gn.appendInterval_adapt ℱ hKn (masterApprox_adapt ℱ H h_meas h_progMeas
    h_sq_int_global n)
  have ha_m := Gm.appendInterval_adapt ℱ hKm (masterApprox_adapt ℱ H h_meas h_progMeas
    h_sq_int_global m)
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (Gn.appendInterval hKn)
    (Gm.appendInterval hKm) h_eq ha_n ha_m ht_nn
  have hL : ∫⁻ ω, (‖simpleIntegral W Gn t ω - simpleIntegral W Gm t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (Gn.appendInterval hKn) t ω
          - simpleIntegral W (Gm.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 Gn) W hKn t ω, (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 Gm) W hKm t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Gn.appendInterval hKn).eval s ω - (Gm.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [(_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 Gn) hKn s ω, (_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 Gm) hKm s ω]
  rw [hL, hR]; exact hiso
/-- `((n : ℝ≥0∞) + 1)⁻¹ → 0`. -/
private lemma tendsto_master_tol :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
  refine this.congr (fun n => ?_)
  simp [Nat.cast_add_one]
end MasterSequence

end LevyStochCalc.Brownian.Ito


