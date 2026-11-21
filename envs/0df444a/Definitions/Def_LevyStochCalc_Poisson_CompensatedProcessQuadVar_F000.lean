-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProcessQuadVar_F000
-- name    : LevyStochCalc_Poisson_CompensatedProcessQuadVar_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:47:07.753553+00:00
-- url     : https://prove2.me/theorems/7a894d17-0013-4732-bcfb-bb9abe41095a
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProcessQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProcessQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F001
import Definitions.Def_SourceProof_7e78553b8746df7092668626

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

/-- The compensator `∫_0^t ∫_E φ(u, e)² ν(de) du` of the integrand. -/
noncomputable def compensator (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ ω u e) ^ 2 ∂ν ∂volume
omit [MeasurableSpace Ω] in
/-- The compensator vanishes at nonpositive times. -/
lemma compensator_of_nonpos {t : ℝ} (ht : t ≤ 0) : compensator ν φ t = fun _ => 0 := by
  funext ω
  unfold compensator
  rw [Measure.restrict_eq_zero.2 (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_of_nonpos (by linarith)), integral_zero_measure]
/-- The product measure of `P`, Lebesgue measure on `[0, t]` and `ν` on `Ω × ℝ × E`. -/
noncomputable abbrev horizonMeasure (P : Measure Ω) (t : ℝ) : Measure (Ω × ℝ × E) :=
  P.prod ((volume.restrict (Set.Icc (0 : ℝ) t)).prod ν)
lemma coe_nnnorm_sq_eq_ofReal_sq (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm _).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
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

omit [IsProbabilityMeasure P] in
/-- The nested triple integral over `Ω`, `[0, t]` and `E` as an integral for the horizon
measure. -/
lemma lintegral_horizonMeasure (t : ℝ) (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) :
    ∫⁻ p, f p.1 p.2.1 p.2.2 ∂(horizonMeasure ν P t)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e, f ω s e ∂ν ∂volume ∂P := by
  rw [horizonMeasure, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_prod (fun y : ℝ × E => f (ω, y).1 (ω, y).2.1 (ω, y).2.2)
    (hf.comp (measurable_prodMk_left (x := ω))).aemeasurable]
include h_progMeas in
/-- The compensator is adapted to the natural filtration. -/
lemma compensator_stronglyAdapted :
    StronglyAdapted ℱ (compensator ν φ) := by
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact (_root_.Prove2MeSourceProof.h_7e78553b8746df7092668626 ((continuous_pow 2).comp_markedProgressivelyMeasurable (by simp)
      h_progMeas)) measurableSet_Icc
      Set.Icc_subset_Iic_self volume ν
  · rw [compensator_of_nonpos ν φ ht.le]
    exact stronglyMeasurable_const
omit [IsProbabilityMeasure P] in
include h_meas h_sq_int_global in
/-- The integrand is square-integrable for the horizon measure. -/
lemma memLp_phi_horizon {t : ℝ} (ht : 0 < t) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) := by
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
    lintegral_horizonMeasure t (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      ((ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2)]
  exact h_sq_int_global t ht
include h_meas h_sq_int_global in
/-- The compensator is integrable at every time. -/
lemma integrable_compensator (t : ℝ) : Integrable (compensator ν φ t) P := by
  rcases le_or_gt t 0 with ht | ht
  · rw [compensator_of_nonpos ν φ ht]
    exact integrable_const 0
  · have hint := (memLp_phi_horizon φ h_meas h_sq_int_global ht).integrable_sq
    refine hint.integral_prod_left.congr ?_
    filter_upwards [hint.prod_right_ae] with ω hω
    exact integral_prod _ hω
/-- The integrand of the stage-`n` approximant as a function on `Ω × ℝ × E`. -/
noncomputable def stageEval (n : ℕ) (p : Ω × ℝ × E) : ℝ :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval p.2.1 p.2.2 p.1
lemma measurable_stageEval (n : ℕ) :
    Measurable (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n) :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable
end LevyStochCalc.Poisson.Compensated


