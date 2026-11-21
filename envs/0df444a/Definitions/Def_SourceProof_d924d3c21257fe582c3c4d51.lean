-- Prove2me | Definitions.Def_SourceProof_d924d3c21257fe582c3c4d51
-- name    : SourceProof_d924d3c21257fe582c3c4d51
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:13:59.432463+00:00
-- url     : https://prove2.me/theorems/82465337-1b98-4e2c-a07d-bdfb4dc49719
-- title:
--   LevyStochCalc source module: SourceProof_d924d3c21257fe582c3c4d51
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stageIntegral_tendsto_process` comes from the `LevyStochCalc.Poisson.CompensatedProcess` module. The staged Lean declaration includes its source proof and dependency references.
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

theorem _root_.Prove2MeSourceProof.h_d924d3c21257fe582c3c4d51 (t : ℝ) :
    Tendsto (fun n => eLpNorm (fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
      t ω
      - process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) 2 P) atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h1 := LevyStochCalc.Poisson.Compensated.stageLp_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
  have hmem : MemLp (↑↑(LevyStochCalc.Poisson.Compensated.processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) 2 P :=
    Lp.memLp _
  rw [← Lp.toLp_coeFn (LevyStochCalc.Poisson.Compensated.processLp N ℱ φ h_meas h_progMeas h_sq_int_global t) hmem] at h1
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun n => LevyStochCalc.Poisson.Compensated.stageLp N ℱ φ h_meas h_progMeas h_sq_int_global t n)
    (↑↑(LevyStochCalc.Poisson.Compensated.processLp N ℱ φ h_meas h_progMeas h_sq_int_global t)) hmem).mp h1
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [LevyStochCalc.Poisson.Compensated.stageLp_coeFn N ℱ φ h_meas h_progMeas h_sq_int_global t n,
    LevyStochCalc.Poisson.Compensated.process_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t] with ω hω hF
  simp only [Pi.sub_apply]
  rw [hω, hF]
end Process

section Isometry

end Isometry

end LevyStochCalc.Poisson.Compensated


