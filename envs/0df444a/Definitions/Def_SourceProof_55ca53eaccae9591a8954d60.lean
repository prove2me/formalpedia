-- Prove2me | Definitions.Def_SourceProof_55ca53eaccae9591a8954d60
-- name    : SourceProof_55ca53eaccae9591a8954d60
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:50:27.836143+00:00
-- url     : https://prove2.me/theorems/267da90f-de2f-439f-869d-ca0026457f78
-- title:
--   LevyStochCalc source module: SourceProof_55ca53eaccae9591a8954d60
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivs_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Definitions.Def_LevyStochCalc_Ito_SdeDataOfSolvesOn_F000
import Definitions.Def_SourceProof_3c18bbf1d33e9f6a14989002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the derived integrands along a path

The two stochastic integrals of the Itô–Lévy formula at bounded derivatives carry the integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` evaluated along a path. For a `C²` state function with bounded
gradient and coefficients that are regular and Lipschitz, each of these is jointly measurable,
progressively measurable in the sense its integral asks for, and of finite energy on every
window; along the path the drift is integrable and the compensator-drift integrand has finite
mark energy, almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section DerivedIntegrands

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {coeffs : JumpDiffusionCoeffs n d E} {u : ℝ → (Fin n → ℝ) → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_55ca53eaccae9591a8954d60 (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₂ : ℝ} (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X))
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤ := by
  have hK₂' : ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  set C : ℝ := (n : ℝ) ^ 2 * max K₂ 0 * n with hC
  have hC0 : 0 ≤ C := by positivity
  -- the pointwise bound, in extended form
  have hpt : ∀ ω s e, (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal C * ∑ i, (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s e
    have hreal : |LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
        ≤ C * ∑ i, coeffs.γ s (X s ω) e i ^ 2 := by
      have h := LevyStochCalc.Ito.JumpFormula.abs_mixedCompensatorDriftIntegrand_le hu (γ := coeffs.γ) hK₂' (le_max_right _ _)
        s (X s ω) (X s ω) e
      rw [hC]
      calc |LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
          ≤ (n : ℝ) ^ 2 * max K₂ 0 * ((n : ℝ) * ∑ i, coeffs.γ s (X s ω) e i ^ 2) := h
        _ = (n : ℝ) ^ 2 * max K₂ 0 * n * ∑ i, coeffs.γ s (X s ω) e i ^ 2 := by ring
    rw [show ((‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞))
        = ‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖ₑ from rfl,
      Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
        ≤ ENNReal.ofReal (C * ∑ i, coeffs.γ s (X s ω) e i ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C * ∑ i, (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun i _ => (LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real _).symm)
  have hm : ∀ i, Measurable fun p : Ω × ℝ × E =>
      (‖coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (((hγm i).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- the energy of the integrand is finite
  have houter : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt
      (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e) ?_
    have hC' : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    simp_rw [lintegral_const_mul' _ _ hC']
    rw [LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sum
      (f := fun i ω s e => (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2) hm T]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.mpr fun i _ => hγq i T hT)
  have hfm : Measurable fun p : Ω × ℝ × E =>
      (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2‖₊ : ℝ≥0∞) :=
    (_root_.Prove2MeSourceProof.h_3c18bbf1d33e9f6a14989002 hu hγ hXm).nnnorm.coe_nnreal_ennreal
  exact ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
    (f := fun ω s e => (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)) hfm T)
    houter.ne
end DerivedIntegrands

end LevyStochCalc.Ito.JumpFormula


