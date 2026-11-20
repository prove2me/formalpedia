-- Prove2me | Definitions.Def_SourceProof_1e6256252a8bd3d3b339a9d9
-- name    : SourceProof_1e6256252a8bd3d3b339a9d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:58:06.876846+00:00
-- url     : https://prove2.me/theorems/0c8688c8-73fe-414c-b435-2b0229cd30ce
-- title:
--   LevyStochCalc source module: SourceProof_1e6256252a8bd3d3b339a9d9
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.dyadicAvg_eq_average_closedBall` comes from the `LevyStochCalc.Poisson.CompensatedDensityDyadic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F001

open private closedBall_eq_Icc from Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F001
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

omit [MeasurableSpace Ω] [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_1e6256252a8bd3d3b339a9d9
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    dyadicAvg T φ n i ω e =
      ⨍ y in Metric.closedBall
        ((dyadicPartition T n i.castSucc + dyadicPartition T n i.succ) / 2)
        ((dyadicPartition T n i.succ - dyadicPartition T n i.castSucc) / 2),
        φ ω y e ∂volume := by
  set t_i := LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.castSucc with ht_i
  set t_succ := LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.succ with ht_succ
  have h_lt : t_i < t_succ := LevyStochCalc.Poisson.Compensated.dyadicPartition_strictMono hT n Fin.castSucc_lt_succ
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) := LevyStochCalc.Poisson.Compensated.dyadicPartition_diff n i
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  rw [closedBall_eq_Icc t_i t_succ,
    show (volume.restrict (Set.Icc t_i t_succ) : Measure ℝ)
        = volume.restrict (Set.Ioc t_i t_succ)
      from MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm,
    MeasureTheory.average_eq]
  unfold LevyStochCalc.Poisson.Compensated.dyadicAvg
  rw [show ((volume.restrict (Set.Ioc t_i t_succ) : Measure ℝ).real Set.univ) = t_succ - t_i from by
        unfold MeasureTheory.Measure.real
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)],
    h_diff]
  have h_T_ne : T ≠ 0 := ne_of_gt hT
  have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
  rw [smul_eq_mul]; field_simp; ring
end LevyStochCalc.Poisson.Compensated


