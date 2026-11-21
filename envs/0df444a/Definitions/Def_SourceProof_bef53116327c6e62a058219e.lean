-- Prove2me | Definitions.Def_SourceProof_bef53116327c6e62a058219e
-- name    : SourceProof_bef53116327c6e62a058219e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:40:43.465181+00:00
-- url     : https://prove2.me/theorems/7d6d6a41-71ce-45e9-9481-3e5e42160290
-- title:
--   LevyStochCalc source module: SourceProof_bef53116327c6e62a058219e
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.weighted_energy_le_of_terminal_zero` comes from the `LevyStochCalc.Ito.SecondMomentBackward` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentBackward_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The backward weighted energy inequality

For an Itô–Lévy process `X` over a Lévy driver that vanishes at a horizon `T`, the exponentially
weighted second moment identity

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`

has vanishing left-hand side and a nonnegative initial term, so the weighted energy of the
process and of its two integrands is dominated by the weighted pairing of the process against
the negated drift,

`∫_0^T e^{βs} (β 𝔼[X_s²] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)) ds
  ≤ ∫_0^T e^{βs} · 2 𝔼[X_s (-b_s)] ds`,

the backward form in which the a-priori estimates for BSDEs with jumps read the quadratic Itô
formula.

## Main statements

* `weighted_energy_le_of_terminal_zero` — the inequality, with the drift negated inside the
  pairing on the right.
* `weighted_energy_le_of_terminal_zero'` — the same with the drift left as it stands and the
  sign carried outside the time integral.
* `integrableOn_integral_mul_self` — the second moment of an Itô–Lévy process is integrable in
  time on every window.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Prelim

end Prelim

section Backward

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_bef53116327c6e62a058219e
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) (hXT : X T =ᵐ[P] 0) :
    ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
        * (β * ∫ ω, X s ω * X s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω, X s ω * (-b s ω) ∂P) := by
  have hA : IntegrableOn (fun s => ∫ ω, X s ω * X s ω ∂P) (Set.Icc (0 : ℝ) T) :=
    LevyStochCalc.Ito.SecondMoment.integrableOn_integral_mul_self h D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq hT
  have hB : IntegrableOn (fun s => ∫ ω, X s ω * b s ω ∂P) (Set.Icc (0 : ℝ) T) :=
    _root_.Prove2MeSourceProof.h_d8b446e22164b7620e52d72e h hX₀2 hbm hbp hbq hT
  have hC : IntegrableOn (fun s => ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    integrable_finsetSum _ fun j _ =>
      LevyStochCalc.Ito.SecondMoment.integrableOn_toReal_lintegral (LevyStochCalc.Ito.SecondMoment.measurable_uncurry_sq_diffusion h j) (h.σ_sq j T hT)
  have hD : IntegrableOn (fun s => (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    LevyStochCalc.Ito.SecondMoment.integrableOn_toReal_lintegral (LevyStochCalc.Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump h) (h.γ_sq T hT)
  have wB : IntegrableOn (fun s => Real.exp (β * s) * (2 * ∫ ω, X s ω * b s ω ∂P))
      (Set.Icc (0 : ℝ) T) := LevyStochCalc.Ito.SecondMoment.integrableOn_exp_mul β (hB.const_mul 2)
  have wACD : IntegrableOn (fun s => Real.exp (β * s)
      * (β * ∫ ω, X s ω * X s ω ∂P
        + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)) (Set.Icc (0 : ℝ) T) := by
    refine (((LevyStochCalc.Ito.SecondMoment.integrableOn_exp_mul β (hA.const_mul β)).add
      (LevyStochCalc.Ito.SecondMoment.integrableOn_exp_mul β hC)).add (LevyStochCalc.Ito.SecondMoment.integrableOn_exp_mul β hD)).congr
      (Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply]
    ring
  have key := LevyStochCalc.Ito.SecondMoment.integral_exp_mul_self_eq_of_isItoLevyProcess_aug h hX₀ hX₀2 hbm hbp hbq β hT
  have hXT2 : ∫ ω, X T ω * X T ω ∂P = 0 := by
    have he : (fun ω => X T ω * X T ω) =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hXT] with ω hω
      simp [hω]
    simpa using integral_congr_ae he
  rw [hXT2, mul_zero] at key
  have hsplit : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
        * (β * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      = (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
          * (β * ∫ ω, X s ω * X s ω ∂P
            + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
            + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal))
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω, X s ω * b s ω ∂P) := by
    rw [← integral_add wACD wB]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    ring
  rw [hsplit] at key
  have hm0 : (0 : ℝ) ≤ ∫ ω, X₀ ω * X₀ ω ∂P := integral_nonneg fun ω => mul_self_nonneg _
  have hrhs : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω, X s ω * (-b s ω) ∂P)
      = -∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω, X s ω * b s ω ∂P) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    have hn : ∫ ω, X s ω * (-b s ω) ∂P = -∫ ω, X s ω * b s ω ∂P := by
      simp only [mul_neg, integral_neg]
    rw [hn]
    ring
  rw [hrhs]
  linarith
end Backward

end LevyStochCalc.Ito.SecondMoment


