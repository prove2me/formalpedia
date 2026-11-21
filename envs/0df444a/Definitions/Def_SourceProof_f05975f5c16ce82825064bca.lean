-- Prove2me | Definitions.Def_SourceProof_f05975f5c16ce82825064bca
-- name    : SourceProof_f05975f5c16ce82825064bca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:09:33.440507+00:00
-- url     : https://prove2.me/theorems/ab3a9240-419b-4d9a-ad8d-cd087fd1e688
-- title:
--   LevyStochCalc source module: SourceProof_f05975f5c16ce82825064bca
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stageIntegral_sub_sq_horizon_le` comes from the `LevyStochCalc.Poisson.CompensatedApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F001
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F002
import Definitions.Def_SourceProof_64b57ddfa082ba813e2cbaf7
import Definitions.Def_SourceProof_8b57cd5261008e75b4f880d6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Approximation of a square-integrable integrand by mark-step integrands

For a jointly measurable, progressively measurable integrand `φ : Ω → ℝ → E → ℝ` that is
square integrable over `Ω × [0, T] × E`, and any dyadic level `L₀` and tolerance `ε`, there is
an adapted mark-step integrand on a dyadic grid of level at least `L₀` within `ε` of `φ` in
`L²(P ⊗ ds ⊗ ν)` on `[0, T]` (`exists_markStep_close`). The integrand is first clipped and
restricted to a mark set of finite measure (`truncate`), which reduces to the bounded,
finitely supported case treated by `exists_markEval_L2_tendsto`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Truncate

variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Truncate

section Close

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)

end Close

section Master

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Master

section Cauchy

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

theorem _root_.Prove2MeSourceProof.h_f05975f5c16ce82825064bca {n n' : ℕ} (h : n ≤ n') :
    ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n (stageHorizon n) ω
        - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' (stageHorizon n) ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := by
  set G := (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hGdef
  set G' := (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n').2 with hG'def
  have hG := LevyStochCalc.Poisson.Compensated.master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n
  have hG' := LevyStochCalc.Poisson.Compensated.master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n'
  have hlev := LevyStochCalc.Poisson.Compensated.master_level_add N ℱ φ h_meas h_progMeas h_sq_int_global h
  have hd : n' - n ≤ (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 := by omega
  have hℓ : (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n).1
      ≤ (LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 - (n' - n) := by omega
  have hT := LevyStochCalc.Poisson.Compensated.stageHorizon_eq_mul h
  set R := G'.dyadicRestrict (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n) hd hT with hRdef
  set Rf := G.dyadicRefine hℓ with hRfdef
  have hR : R.Adapted ℱ := hG'.dyadicRestrict (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n) hd hT
  have hRf : Rf.Adapted ℱ := hG.dyadicRefine N hℓ
  have hhor : (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (LevyStochCalc.Poisson.Compensated.stageHorizon n) (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n)
      ((LevyStochCalc.Poisson.Compensated.master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 - (n' - n))).horizon
      = LevyStochCalc.Poisson.Compensated.stageHorizon n := LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon _ _ _
  have e1 : ∀ ω, LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω
      = G.full N ω := fun ω =>
    G.integral_eq_full_of_horizon_le N (by rw [LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon]) ω
  have e2 : ∀ ω, LevyStochCalc.Poisson.Compensated.stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω
      = R.full N ω := fun ω => (G'.full_dyadicRestrict N (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n) hd hT ω).symm
  have e3 : ∀ ω, R.full N ω = R.integral N (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω := fun ω =>
    (R.integral_eq_full_of_horizon_le N hhor.le ω).symm
  have e4 : ∀ ω, Rf.full N ω = Rf.integral N (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω := fun ω =>
    (Rf.integral_eq_full_of_horizon_le N hhor.le ω).symm
  have hae : (fun ω => (‖G.full N ω - R.full N ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖Rf.integral N (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω
        - R.integral N (LevyStochCalc.Poisson.Compensated.stageHorizon n) ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [G.full_dyadicRefine N hℓ] with ω hω
    rw [← hω, e3, e4]
  simp_rw [e1, e2]
  rw [lintegral_congr_ae hae,
    Rf.lintegral_integral_sub_sq_at N hℱ R hRf hR (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n).le]
  have hev : ∀ ω e s, s ∈ Set.Icc (0 : ℝ) (LevyStochCalc.Poisson.Compensated.stageHorizon n) →
      Rf.eval s e ω - R.eval s e ω = G.eval s e ω - G'.eval s e ω := by
    intro ω e s hs
    rw [G.eval_dyadicRefine hℓ, (_root_.Prove2MeSourceProof.h_8b57cd5261008e75b4f880d6 G') (LevyStochCalc.Poisson.Compensated.stageHorizon_pos n) hd hT hs.2]
  have hu : Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.sub G.eval_measurable).nnnorm).pow_const 2
  have hw : Measurable (fun p : Ω × ℝ × E =>
      (‖G.eval p.2.1 p.2.2 p.1 - G'.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp
      (G.eval_measurable.sub G'.eval_measurable).nnnorm).pow_const 2
  have hpt : ∀ ω s e, (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
        + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s e
    rw [show G.eval s e ω - G'.eval s e ω
      = -(φ ω s e - G.eval s e ω) + (φ ω s e - G'.eval s e ω) by ring]
    have h2 := LevyStochCalc.Poisson.Compensated.sq_nnnorm_add_le_two_mul (-(φ ω s e - G.eval s e ω)) (φ ω s e - G'.eval s e ω)
    rwa [nnnorm_neg] at h2
  have herr' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (LevyStochCalc.Poisson.Compensated.stageHorizon n), ∫⁻ e,
      (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ LevyStochCalc.Poisson.Compensated.stageErr φ P n' G' :=
    lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right (LevyStochCalc.Poisson.Compensated.stageHorizon_mono h))
  calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) (LevyStochCalc.Poisson.Compensated.stageHorizon n),
        (‖Rf.eval s e ω - R.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (LevyStochCalc.Poisson.Compensated.stageHorizon n), ∫⁻ e,
        (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [← LevyStochCalc.Poisson.Compensated.lintegral_swap_es (fun ω s e => (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hw ω]
        refine lintegral_congr fun e => ?_
        refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        rw [hev ω e s hs]
    _ ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (LevyStochCalc.Poisson.Compensated.stageHorizon n), ∫⁻ e,
        2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
          + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) ∂ν ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e
    _ = 2 * (LevyStochCalc.Poisson.Compensated.stageErr φ P n G + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (LevyStochCalc.Poisson.Compensated.stageHorizon n), ∫⁻ e,
        (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
        rw [LevyStochCalc.Poisson.Compensated.lintegral_triple_const_mul 2 (by norm_num), _root_.Prove2MeSourceProof.h_64b57ddfa082ba813e2cbaf7 hu]
        rfl
    _ ≤ 2 * (((n : ℝ≥0∞) + 1)⁻¹ + ((n' : ℝ≥0∞) + 1)⁻¹) := by
        gcongr
        · exact (LevyStochCalc.Poisson.Compensated.master_err N ℱ φ h_meas h_progMeas h_sq_int_global n).le
        · exact herr'.trans (LevyStochCalc.Poisson.Compensated.master_err N ℱ φ h_meas h_progMeas h_sq_int_global n').le
    _ = 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := mul_add _ _ _
end Cauchy

end LevyStochCalc.Poisson.Compensated


