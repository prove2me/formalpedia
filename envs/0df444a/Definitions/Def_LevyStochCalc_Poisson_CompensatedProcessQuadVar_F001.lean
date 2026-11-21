-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F001
-- name    : LevyStochCalc_Poisson_CompensatedProcessQuadVar_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:53:03.914185+00:00
-- url     : https://prove2.me/theorems/85d0ee7a-1ee9-4169-b3d6-f085ba0ac01e
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedProcessQuadVar
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedProcessQuadVar in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral process

The compensated square `t ↦ F_t² − ∫_0^t ∫_E φ(u, e)² ν(de) du` of the `L²` integral process
`F` is a martingale on the filtration `ℱ` of the integral and on its right-continuation `ℱ₊`,
`ℱ₊ t = ⨅ s > t, ℱ s` (no null sets are added). The stage compensated squares are martingales
(`MarkStep.martingale_sq_sub_compensator`) and converge in `L¹` to the compensated square of the
process: the stage integrands converge to `φ` in `L²` of the product measure on
`Ω × [0, t] × E`, so their squares converge in `L¹`, and the `L¹(P)`-distance of the compensators
is dominated by the joint `L¹`-distance.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Compensator

variable (ν : Measure E) (φ : Ω → ℝ → E → ℝ)

end Compensator

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The stage integrands are square-integrable for the horizon measure. -/
lemma memLp_stageEval (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n) 2 (horizonMeasure ν P t) := by
  refine ⟨(measurable_stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n).aestronglyMeasurable,
    ?_⟩
  refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq]
  unfold stageEval
  set G := (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
  have hm : Measurable (fun p : Ω × ℝ × E => (‖G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp G.eval_measurable.nnnorm).pow_const 2
  rw [lintegral_horizonMeasure t (fun ω s e => (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm]
  have h1 := G.lintegral_integral_sq_at N hℱ (master_adapted N ℱ φ h_meas h_progMeas
    h_sq_int_global n)
    ht
  have h2 : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e, (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P :=
    lintegral_congr fun ω =>
      (lintegral_swap_es (fun ω s e => (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm ω).symm
  rw [h2, ← h1, ← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (G.memLp_integral N t).eLpNorm_ne_top
end LevyStochCalc.Poisson.Compensated


