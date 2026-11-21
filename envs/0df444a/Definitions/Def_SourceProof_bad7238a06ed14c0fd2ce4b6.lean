-- Prove2me | Definitions.Def_SourceProof_bad7238a06ed14c0fd2ce4b6
-- name    : SourceProof_bad7238a06ed14c0fd2ce4b6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:41.445177+00:00
-- url     : https://prove2.me/theorems/8aba4776-a1cf-4e4c-af36-fe0d1a91bc8c
-- title:
--   LevyStochCalc source module: SourceProof_bad7238a06ed14c0fd2ce4b6
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` comes from the `LevyStochCalc.Ito.JumpSplitting` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F001
import Definitions.Def_SourceProof_6572ebe1e254a873e7002b18

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting of a jump diffusion

A jump diffusion whose jump coefficient is carried by a mark set of finite intensity is the sum
of a vector Itô process and a pathwise jump sum. The compensated Poisson integral of such a
coefficient is the pathwise integral against the random measure minus the integral against the
reference intensity, and the latter is an absolutely continuous drift, so it can be absorbed into
the drift of the Itô part.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.jumpSum` — the pathwise sum of the jumps carried by a mark set
  over a time window.
* `LevyStochCalc.Ito.JumpSplitting.continuousDrift` — the drift of a jump diffusion with the jump
  compensator subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` — at every nonnegative time a
  jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and drift
  `continuousDrift`, and the pathwise jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section ENNRealAux

end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)

end Regularity

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)


theorem _root_.Prove2MeSourceProof.h_bad7238a06ed14c0fd2ce4b6
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDrift X A) t ω i
          + jumpSum X A t ω i := by
  have hsupp' : ∀ (i : Fin n) (ω : Ω) (s : ℝ) (e : E), e ∉ A →
      coeffs.γ s (X.X s ω) e i = 0 := by
    intro i ω s e he
    simp [hsupp s (X.X s ω) e he]
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have hCzero : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) 0 ω = 0 := by
      intro i
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) 0,
        _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i)
          (le_refl (0 : ℝ))] with ω h1 h2
      rw [h1, h2]
      rfl
    have hz0 : ∀ g : ℝ → ℝ, ∫ s in Set.Icc (0 : ℝ) 0, g s ∂volume = 0 :=
      fun g => setIntegral_measure_zero g (by simp)
    filter_upwards [hSDE 0 le_rfl, MeasureTheory.ae_all_iff.mpr hCzero] with ω hω hz
    intro i
    rw [hω i, hz i, LevyStochCalc.Ito.JumpSplitting.multidimIntegral_eq_vectorItoMartingale X ℱ hℱW hσm hσp hσq i 0 ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, hz0, LevyStochCalc.Ito.JumpSplitting.jumpSum_zero]
  · have hpath : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω
          = LevyStochCalc.Ito.JumpSplitting.jumpSum X A t ω i
            - ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i
                ∂(LevyStochCalc.Poisson.referenceIntensity ν) := fun i =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱN
        (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) hA (hpred i) hAν
        (hsupp' i) hpos
    have hwin : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
          (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [_root_.Prove2MeSourceProof.h_6572ebe1e254a873e7002b18 N hℱN hA hAν t (hpred i)
        (hγm i) (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγq i) (A := A) hpos)] with ω hω
      exact hω.2
    have hμint : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) t) volume := by
      intro i
      have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        ((ENNReal.continuous_coe.measurable.comp (hμm i).nnnorm).pow_const
          2).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      filter_upwards [ae_lt_top' hmeas.aemeasurable (hμq i t hpos).ne] with ω hω
      exact LevyStochCalc.Ito.JumpSplitting.integrableOn_Icc_of_lintegral_sq_lt_top
        ((hμm i).comp measurable_prodMk_left).aestronglyMeasurable hω
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hSDE t ht, hpath i, hwin i, hμint i] with ω hω hp hw hm
    obtain ⟨heq, hcint⟩ :=
      LevyStochCalc.Ito.JumpSplitting.integral_window_eq_and_integrableOn (fun s e => coeffs.γ s (X.X s ω) e i) hw
    have hd : ∫ s in Set.Icc (0 : ℝ) t, LevyStochCalc.Ito.JumpSplitting.continuousDrift X A i ω s ∂volume
        = (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, (∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν) ∂volume :=
      integral_sub hm hcint
    rw [hω i, hp, LevyStochCalc.Ito.JumpSplitting.multidimIntegral_eq_vectorItoMartingale X ℱ hℱW hσm hσp hσq i t ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    rw [hd, heq]
    ring
end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting


