-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:35:04.801343+00:00
-- url     : https://prove2.me/theorems/3adca50a-e62e-47ac-abe9-28060db1c718
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Probability_MarkedProgressiveSlice_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the mixed integrands of the Itô–Lévy formula

The mixed integrands of the Itô–Lévy formula along a jump diffusion — the derivatives of a `C²`
state function read at an auxiliary path, the coefficients read at the solution — are jointly
measurable, are progressively measurable for the right-continuous regularisation of the
filtration of the SDE data, and have finite energy on every bounded window; over that
regularisation the Brownian and the compensated jump integral agree almost surely with the ones
over the filtration itself, and the endpoint of a path together with its two stochastic
integrals is measurable componentwise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The compensated jump integral over the right-continuous regularisation of the filtration of
the SDE data agrees almost surely with the one over that filtration. -/
theorem compensatedStochasticIntegral_rightCont_ae_eq (S : SdeData X)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont) (Φ : Ω → ℝ → E → ℝ)
    (hΦm : Measurable fun p : Ω × ℝ × E => Φ p.1 p.2.1 p.2.2)
    (hΦp : Probability.MarkedProgressivelyMeasurable S.ℱ Φ)
    (hΦp' : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont Φ)
    (hΦq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖Φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (T : ℝ) :
    stochasticIntegral N S.ℱ.rightCont h𝒢N Φ hΦm hΦp' hΦq T
      =ᵐ[P] stochasticIntegral N S.ℱ S.isPoisson Φ hΦm hΦp hΦq T :=
  (stochasticIntegral_congr_filtration N S.ℱ S.ℱ.rightCont S.isPoisson h𝒢N
    (fun t => S.ℱ.le_rightCont t) _ hΦm hΦp hΦp' hΦq T).symm
/-- The endpoint of an auxiliary path, the Brownian integrals of the mixed diffusion integrands
along it and the compensated integral of its cut mixed jump increment are measurable
componentwise. -/
theorem measurable_sumElim_mixedTerms (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont)
    (y : ℝ → Ω → Fin n → ℝ) (hy : Measurable (Function.uncurry y)) (A : Set E)
    (hBm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j))
    (hBp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
    (hBq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hCm : Measurable fun p : Ω × ℝ × E => markCut A
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hCp : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont (markCut A
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e))
    (hCq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut A (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) ω s e‖₊ :
        ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (c : Fin n ⊕ Fin d ⊕ Unit) :
    Measurable (Sum.elim (fun i ω => y T ω i) (Sum.elim
      (fun j ω => stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
        (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
        (hBm j) (hBp j) (hBq j) T ω)
      (fun _ ω => stochasticIntegral N S.ℱ.rightCont h𝒢N (markCut A
          fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
        hCm hCp hCq T ω)) c) := by
  rcases c with i | j | _
  · exact (measurable_pi_apply i).comp (hy.comp (measurable_const.prodMk measurable_id))
  · exact ((stochasticIntegralBrownian_stronglyAdapted (W.W j) S.ℱ.rightCont (h𝒢W j)
      (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
      (hBm j) (hBp j) (hBq j) T).mono
        (S.ℱ.rightCont.le T)).measurable
  · exact (stochasticIntegral_adapted N S.ℱ.rightCont h𝒢N _ hCm hCp hCq T).mono
      (S.ℱ.rightCont.rightCont.le T) le_rfl
/-- The endpoint of the solution, the Brownian integrals of the diffusion integrands along it
and the compensated integral of its jump increment are measurable componentwise. -/
theorem measurable_sumElim_solutionTerms (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hjm : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (hjp : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont
        (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')))
    (hjq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (c : Fin n ⊕ Fin d ⊕ Unit) :
    Measurable (Sum.elim (fun i ω => X.X T ω i) (Sum.elim
      (fun j ω => stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
        (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
        (hσm j) (hσp j) (hσq j) T ω)
      (fun _ ω => stochasticIntegral N S.ℱ.rightCont h𝒢N
        (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
        hjm hjp hjq T ω)) c) := by
  rcases c with i | j | _
  · exact (measurable_pi_apply i).comp (X.measurable_path.comp
      (measurable_const.prodMk measurable_id))
  · exact ((stochasticIntegralBrownian_stronglyAdapted (W.W j) S.ℱ.rightCont (h𝒢W j)
      (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
      (hσm j) (hσp j) (hσq j) T).mono
        (S.ℱ.rightCont.le T)).measurable
  · exact (stochasticIntegral_adapted N S.ℱ.rightCont h𝒢N _ hjm hjp hjq T).mono
      (S.ℱ.rightCont.rightCont.le T) le_rfl
end Mixed

end LevyStochCalc.Ito.JumpFormula


