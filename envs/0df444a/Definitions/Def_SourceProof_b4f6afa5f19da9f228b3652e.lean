-- Prove2me | Definitions.Def_SourceProof_b4f6afa5f19da9f228b3652e
-- name    : SourceProof_b4f6afa5f19da9f228b3652e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:47:13.824378+00:00
-- url     : https://prove2.me/theorems/48254a54-1912-4c5c-b734-fdd09d2c7fd3
-- title:
--   LevyStochCalc source module: SourceProof_b4f6afa5f19da9f228b3652e
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_eq_expand` comes from the `LevyStochCalc.Ito.SecondMomentBilinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear second moment of two Itô–Lévy processes

For two Itô–Lévy processes `X` and `Y` over the same Lévy driver, with coefficients
`(X₀, b, σ, γ)` and `(Y₀, b', σ', γ')` satisfying the `L²` hypotheses, the expected product at a
time `T > 0` is

`𝔼[X_T Y_T] = 𝔼[X₀ Y₀] + ∫_0^T 𝔼[X_s b'_s + Y_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j σ'_j ds
  + 𝔼 ∫_0^T ∫_E γ γ' dν ds`,

the expectation form of the bilinear Itô formula, obtained from the polarised isometries of the
two stochastic integrals and the polarised drift identity. The drift term is the time integral of
the expected pairing; at every time the pairing is expanded along the decomposition, and the two
martingale pieces are read at the horizon by the martingale property.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Bilinear

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_b4f6afa5f19da9f228b3652e
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (hX₀2 : MemLp X₀ 2 P) (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {s T : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g)
    (hg2 : MemLp g 2 P) :
    ∫ ω, X s ω * g ω ∂P
      = ∫ ω, g ω * X₀ ω ∂P + ∫ ω, g ω * (∫ r in Set.Icc (0 : ℝ) s, b r ω) ∂P
        + (∑ j, ∫ ω, g ω * LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j)
            (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) T ω ∂P)
        + ∫ ω, g ω * LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas
            h.γ_prog h.γ_sq T ω ∂P := by
  classical
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  set Dr : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω with hDrdef
  have hdec : ∀ᵐ ω ∂P, X s ω = X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω := h.decomposition s hs0
  have hS2 : ∀ (j : Fin d) (t : ℝ), MemLp (S j t) 2 P := fun j t =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hC2 : ∀ t, MemLp (C t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hDr2 : MemLp (Dr s) 2 P :=
    LevyStochCalc.Ito.SecondMoment.memLp_two_setIntegral (f := fun ω s => b s ω) hbm hs0
      (LevyStochCalc.Ito.SecondMoment.energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq hs0)
  have hg' : StronglyMeasurable[ℱ.rightCont s] g := hg.mono (ℱ.le_rightCont s)
  have h1 : ∫ ω, X s ω * g ω ∂P
      = ∫ ω, (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * g ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hdec] with ω hω
    rw [hω]
  have hexp : (fun ω => (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * g ω)
      = fun ω => g ω * X₀ ω + g ω * Dr s ω + (∑ j, g ω * S j s ω) + g ω * C s ω := by
    funext ω
    rw [← Finset.mul_sum]
    ring
  have i1 : Integrable (fun ω => g ω * X₀ ω) P := hg2.integrable_mul hX₀2
  have i2 : Integrable (fun ω => g ω * Dr s ω) P := hg2.integrable_mul hDr2
  have i3 : ∀ j, Integrable (fun ω => g ω * S j s ω) P := fun j => hg2.integrable_mul (hS2 j s)
  have i3' : Integrable (fun ω => ∑ j, g ω * S j s ω) P := integrable_finsetSum _ fun j _ => i3 j
  have i4 : Integrable (fun ω => g ω * C s ω) P := hg2.integrable_mul (hC2 s)
  have i12 : Integrable (fun ω => g ω * X₀ ω + g ω * Dr s ω) P := i1.add i2
  have i123 : Integrable (fun ω => g ω * X₀ ω + g ω * Dr s ω + ∑ j, g ω * S j s ω) P :=
    i12.add i3'
  have hSj : ∀ j, ∫ ω, g ω * S j s ω ∂P = ∫ ω, g ω * S j T ω ∂P := fun j =>
    (LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq
      (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j)) hsT hg' hg2 (hS2 j T)).symm
  have hCproc : ∀ t, C t =ᵐ[P]
      LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t :=
    fun t => LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN γ
      h.γ_meas h.γ_prog h.γ_sq t
  have hCs : ∫ ω, g ω * C s ω ∂P = ∫ ω, g ω * C T ω ∂P := by
    have e1 : (fun ω => g ω * C s ω) =ᵐ[P] fun ω => g ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq s ω := by
      filter_upwards [hCproc s] with ω hω
      rw [hω]
    have e2 : (fun ω => g ω * C T ω) =ᵐ[P] fun ω => g ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
      filter_upwards [hCproc T] with ω hω
      rw [hω]
    rw [integral_congr_ae e1, integral_congr_ae e2]
    exact (LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq
      (_root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq)
      hsT hg hg2
      (LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T)).symm
  rw [h1, hexp, integral_add i123 i4, integral_add i12 i3', integral_add i1 i2,
    integral_finsetSum _ fun j _ => i3 j, hCs]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun j _ => hSj j
end Bilinear

end LevyStochCalc.Ito.SecondMoment


