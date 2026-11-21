-- Prove2me | Definitions.Def_SourceProof_2c4e2697eef458aa9c0dbb56
-- name    : SourceProof_2c4e2697eef458aa9c0dbb56
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:13:38.173309+00:00
-- url     : https://prove2.me/theorems/d4ffa0a3-498b-476b-9f2a-f5ef13993109
-- title:
--   LevyStochCalc source module: SourceProof_2c4e2697eef458aa9c0dbb56
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos` comes from the `LevyStochCalc.Poisson.CompensatedProcess` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

include hℱ in

theorem _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 {t : ℝ} (ht : t ≤ 0) :
    process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  have hst : ∀ n, LevyStochCalc.Poisson.Compensated.stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n = 0 := by
    intro n
    rw [Lp.eq_zero_iff_ae_eq_zero]
    refine (LevyStochCalc.Poisson.Compensated.stageLp_coeFn N ℱ φ h_meas h_progMeas h_sq_int_global t n).trans
      (Eventually.of_forall fun ω => ?_)
    exact LevyStochCalc.Poisson.Compensated.stageIntegral_eq_zero_of_nonpos N ℱ φ h_meas h_progMeas h_sq_int_global n ht ω
  have hlim : LevyStochCalc.Poisson.Compensated.processLp N ℱ φ h_meas h_progMeas h_sq_int_global t = 0 := by
    have h := LevyStochCalc.Poisson.Compensated.stageLp_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
    simp only [hst] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  refine (LevyStochCalc.Poisson.Compensated.process_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).trans ?_
  rw [hlim]
  exact Lp.coeFn_zero ℝ 2 P
end Process

section Isometry

end Isometry

end LevyStochCalc.Poisson.Compensated


