-- Prove2me | Definitions.Def_SourceProof_5095b5211df9eef5b8388a53
-- name    : SourceProof_5095b5211df9eef5b8388a53
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:49:17.441067+00:00
-- url     : https://prove2.me/theorems/9f43883b-f994-4194-9a5d-70229090726c
-- title:
--   LevyStochCalc source module: SourceProof_5095b5211df9eef5b8388a53
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensator_right_tendsto_L1` comes from the `LevyStochCalc.Poisson.CompensatedProcessQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
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

include h_meas h_sq_int_global in

theorem _root_.Prove2MeSourceProof.h_5095b5211df9eef5b8388a53 (s : ℝ) :
    Tendsto (fun r => eLpNorm (fun ω => compensator ν φ r ω - compensator ν φ s ω) 1 P)
      (𝓝[>] s) (𝓝 0) := by
  rcases le_or_gt 0 s with hs | hs
  · have hslab := _root_.Prove2MeSourceProof.h_7a12160ca4d56ce7d0871bc7 (P := P)
      (LevyStochCalc.Poisson.Compensated.markSq (ν := ν) φ) (LevyStochCalc.Poisson.Compensated.measurable_markSq φ h_meas) hs (lt_add_one s)
      (LevyStochCalc.Poisson.Compensated.horizonInt_lt_top φ h_sq_int_global (s + 1)).ne
    refine hslab.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hsr : s ≤ r := hr.le
    have hint := (LevyStochCalc.Poisson.Compensated.memLp_phi_horizon φ h_meas h_sq_int_global (hs.trans_lt hr)).integrable_sq
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine (lintegral_congr_ae ?_).symm
    filter_upwards [hint.prod_right_ae] with ω hω
    have hu : Integrable (fun u => ∫ e, (φ ω u e) ^ 2 ∂ν) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
      hω.integral_prod_left
    have hus : IntegrableOn (fun u => ∫ e, (φ ω u e) ^ 2 ∂ν) (Set.Icc (0 : ℝ) s) volume :=
      hu.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right hsr) le_rfl)
    have hsub : Set.Ioc s r ⊆ Set.Icc (0 : ℝ) r :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)
    have huc : IntegrableOn (fun u => ∫ e, (φ ω u e) ^ 2 ∂ν) (Set.Ioc s r) volume :=
      hu.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hsplit : LevyStochCalc.Poisson.Compensated.compensator ν φ r ω - LevyStochCalc.Poisson.Compensated.compensator ν φ s ω
        = ∫ u in Set.Ioc s r, ∫ e, (φ ω u e) ^ 2 ∂ν ∂volume := by
      unfold LevyStochCalc.Poisson.Compensated.compensator
      rw [← Set.Icc_union_Ioc_eq_Icc hs hsr, setIntegral_union
        (Set.disjoint_left.2 fun x hx hx' => not_le.2 hx'.1 hx.2) measurableSet_Ioc hus huc]
      ring
    have hnn : ∀ u, 0 ≤ ∫ e, (φ ω u e) ^ 2 ∂ν := fun u => integral_nonneg fun _ => sq_nonneg _
    rw [hsplit, Real.enorm_eq_ofReal (integral_nonneg fun u => hnn u),
      ofReal_integral_eq_lintegral_ofReal huc (Eventually.of_forall hnn)]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioc s r)), Integrable (fun e => (φ ω u e) ^ 2) ν :=
      ae_restrict_of_ae_restrict_of_subset hsub hω.prod_right_ae
    filter_upwards [hae] with u hu'
    rw [ofReal_integral_eq_lintegral_ofReal hu' (Eventually.of_forall fun e => sq_nonneg _),
      LevyStochCalc.Poisson.Compensated.markSq]
    exact lintegral_congr fun e => (LevyStochCalc.Poisson.Compensated.coe_nnnorm_sq_eq_ofReal_sq _).symm
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [show (fun ω => LevyStochCalc.Poisson.Compensated.compensator ν φ r ω - LevyStochCalc.Poisson.Compensated.compensator ν φ s ω) = (0 : Ω → ℝ) from by
      funext ω
      rw [LevyStochCalc.Poisson.Compensated.compensator_of_nonpos ν φ hr.2.le, LevyStochCalc.Poisson.Compensated.compensator_of_nonpos ν φ hs.le]
      simp]
    exact eLpNorm_zero
end LevyStochCalc.Poisson.Compensated


