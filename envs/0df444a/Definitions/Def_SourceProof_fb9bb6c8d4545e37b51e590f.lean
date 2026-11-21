-- Prove2me | Definitions.Def_SourceProof_fb9bb6c8d4545e37b51e590f
-- name    : SourceProof_fb9bb6c8d4545e37b51e590f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:43:31.496745+00:00
-- url     : https://prove2.me/theorems/af9c5680-3f31-483f-8621-010d25ee183c
-- title:
--   LevyStochCalc source module: SourceProof_fb9bb6c8d4545e37b51e590f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_eq_average_closedBall` comes from the `LevyStochCalc.Brownian.ItoDensityShiftedAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002

open private closedBall_eq_Icc from Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable.

-- `omit` the unused `[MeasurableSpace Ω]` section variable.
omit [MeasurableSpace Ω] in

theorem _root_.Prove2MeSourceProof.h_fb9bb6c8d4545e37b51e590f
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    dyadicAvg_brownian (T := T) g n i ω =
      ⨍ y in Metric.closedBall
        ((dyadicPartition_brownian T n i.castSucc + dyadicPartition_brownian T n i.succ) / 2)
        ((dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc) / 2),
        g ω y ∂volume := by
  set t_i := LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i.castSucc with ht_i
  set t_succ := LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    LevyStochCalc.Brownian.Ito.dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) :=
    LevyStochCalc.Brownian.Ito.dyadicPartition_brownian_diff n i
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  -- closedBall (midpoint) (halfLen) = Icc t_i t_succ.
  have h_ball_eq : Metric.closedBall ((t_i + t_succ) / 2) ((t_succ - t_i) / 2) =
      Set.Icc t_i t_succ := closedBall_eq_Icc t_i t_succ
  rw [h_ball_eq]
  -- ⨍ Icc = ⨍ Ioc (since vol({t_i}) = 0).
  rw [show (volume.restrict (Set.Icc t_i t_succ) : Measure ℝ)
        = volume.restrict (Set.Ioc t_i t_succ)
      from MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm]
  -- Now ⨍ over Ioc = (1/vol(Ioc)) * ∫ over Ioc.
  rw [MeasureTheory.average_eq]
  -- dyadicAvg = (2^n/T) * ∫ over Ioc.
  unfold LevyStochCalc.Brownian.Ito.dyadicAvg_brownian
  rw [show ((volume.restrict (Set.Ioc t_i t_succ) : Measure ℝ).real Set.univ)
      = t_succ - t_i from by
    unfold MeasureTheory.Measure.real
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]]
  rw [h_diff]
  -- (T/2^n)⁻¹ * ∫ ... = (2^n/T) * ∫ ...
  have h_T_ne : T ≠ 0 := ne_of_gt hT
  have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
  rw [smul_eq_mul]
  field_simp
  ring
end LevyStochCalc.Brownian.Ito


