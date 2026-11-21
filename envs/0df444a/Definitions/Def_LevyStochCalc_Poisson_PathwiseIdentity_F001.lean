-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001
-- name    : LevyStochCalc_Poisson_PathwiseIdentity_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:39.026307+00:00
-- url     : https://prove2.me/theorems/70f0d84d-4842-4c67-a5b0-73185941a926
-- title:
--   Source declarations: LevyStochCalc.Poisson.PathwiseIdentity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PathwiseIdentity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F000
import Definitions.Def_SourceProof_2c6d8899dc3ae98e013287f2
import Definitions.Def_SourceProof_6984d0dce12206fd688ba936
import Definitions.Def_SourceProof_a5a8473806f22ea94816f7db

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a predictable integrand is pathwise

The compensated integral is an `L²` limit of the integrals of mark-step approximants. For a
predictable integrand carried by a window of finite intensity the approximants can be taken
inside that window, where the reference intensity compensates the counts, so their pathwise forms
converge in mean to the pathwise form of the integrand while their integrals converge in `L²` to
the compensated integral. The two limits therefore agree.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Assembly

variable (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  {A : Set E} (hA : MeasurableSet A)

include hA in
/-- **The compensated integral of a predictable integrand carried by a window of finite
intensity is the difference of the pathwise integrals against the random measure and against
the reference intensity.** -/
theorem process_ae_eq_pathwise (hφpred : Probability.MarkedPredictable ℱ ν φ) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    process N ℱ hℱ φ h_meas h_progMeas h_sq T
      =ᵐ[P] fun ω => (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(referenceIntensity ν) := by
  have hφen := window_energy_ne_top φ h_meas h_sq (A := A) hT
  exact _root_.Prove2MeSourceProof.h_6984d0dce12206fd688ba936
    (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq T).aestronglyMeasurable
    ((_root_.Prove2MeSourceProof.h_2c6d8899dc3ae98e013287f2 N hℱ hA hAν T hφpred h_meas hφen).sub
      (stronglyMeasurable_pathwise_intensity h_meas A T).aestronglyMeasurable)
    (fun n => (MarkStep.memLp_integral N
      (restrictedStage N ℱ φ h_meas h_progMeas h_sq hA n) T).aestronglyMeasurable)
    (tendsto_lintegral_process_sub_restrictedStage N ℱ hℱ φ h_meas h_progMeas h_sq hA hsupp hT)
    (_root_.Prove2MeSourceProof.h_a5a8473806f22ea94816f7db N ℱ hℱ φ h_meas h_progMeas h_sq hA
      hφpred hAν hsupp hT)
include hA in
/-- **The `L²` Itô–Lévy integral of a predictable integrand carried by a window of finite
intensity is pathwise.** -/
theorem stochasticIntegral_ae_eq_pathwise (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hAν : ν A ≠ ⊤) (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T
      =ᵐ[P] fun ω => (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(referenceIntensity ν) :=
  (stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq T).trans
    (process_ae_eq_pathwise N ℱ hℱ φ h_meas h_progMeas h_sq hA hφpred hAν hsupp hT)
end Assembly

end LevyStochCalc.Poisson.Compensated


