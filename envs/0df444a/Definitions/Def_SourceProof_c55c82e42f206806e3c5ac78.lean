-- Prove2me | Definitions.Def_SourceProof_c55c82e42f206806e3c5ac78
-- name    : SourceProof_c55c82e42f206806e3c5ac78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:41:18.673315+00:00
-- url     : https://prove2.me/theorems/def7da2a-4da0-4035-8859-ceceae1e1768
-- title:
--   LevyStochCalc source module: SourceProof_c55c82e42f206806e3c5ac78
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_lintegral_sq_mixedCompensatedIntegral_sub` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limit steps of the Itô–Lévy formula at bounded derivatives

Along a family of paths converging to the solution of a jump diffusion at almost every time of a
window, the four term families of the Itô–Lévy formula converge to their counterparts along the
solution: the Brownian integrals of the mixed diffusion integrands and the compensated integrals
of the cut mixed jump increments converge in `L²`, and the mixed drift and compensator-drift
integrals converge almost surely. The compensator-drift step rests on a form of dominated
convergence for a mark integral over a shrinking family of cuts in which the domination and the
pointwise convergence are asked at almost every time of the window only.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DominatedAe

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end DominatedAe

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

open LevyStochCalc.Ito.IntegralLimit in

theorem _root_.Prove2MeSourceProof.h_c55c82e42f206806e3c5ac78 (S : SdeData X)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (ψ : ℕ → ℕ) (hψ : ∀ k, k ≤ ψ k)
    (hym : ∀ k, Measurable fun p : Ω × ℝ × E => markCut (smallMarks ν (ψ k))ᶜ
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hyp : ∀ k, Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont (markCut
      (smallMarks ν (ψ k))ᶜ fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e))
    (hyq : ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut (smallMarks ν (ψ k))ᶜ
        (fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e) ω s e‖₊ :
          ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
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
    (T : ℝ) (hT : 0 < T)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => y k s ω) atTop (𝓝 (X.X s ω))) :
    Tendsto (fun k => ∫⁻ ω,
      (‖stochasticIntegral N S.ℱ.rightCont h𝒢N (markCut (smallMarks ν (ψ k))ᶜ
            fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e)
          (hym k) (hyp k) (hyq k) T ω
        - stochasticIntegral N S.ℱ.rightCont h𝒢N
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          hjm hjp hjq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
  refine LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated
    N S.ℱ.rightCont h𝒢N
    (fun k => LevyStochCalc.Poisson.Compensated.markCut (LevyStochCalc.Ito.JumpFormula.smallMarks ν (ψ k))ᶜ
      fun ω s e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e)
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    (fun ω s e => (n : ℝ) * c * ∑ i, |coeffs.γ s (X.X s ω) e i|)
    hym hyp hyq hjm hjp hjq ?_ hT ?_ ?_ ?_
  · exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (S.γ_meas i).abs)
  · filter_upwards [hpath] with ω hω
    filter_upwards [hω] with s hs
    filter_upwards [LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp (LevyStochCalc.Ito.JumpFormula.antitone_smallMarks ν)
      (LevyStochCalc.Ito.JumpFormula.measure_iInter_smallMarks ν) hψ] with e he
    have hlim : Tendsto
        (fun k => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e) atTop
        (𝓝 (LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (X.X s ω) (X.X s ω) e)) :=
      LevyStochCalc.Ito.JumpFormula.tendsto_mixedJumpIncrement_of_tendsto hu coeffs.γ s _ e hs
    refine hlim.congr' ?_
    filter_upwards [he] with k hk
    simp [LevyStochCalc.Poisson.Compensated.markCut, hk]
  · intro k
    refine Eventually.of_forall fun ω => Eventually.of_forall fun s =>
      Eventually.of_forall fun e => ?_
    rw [Real.norm_eq_abs]
    exact (LevyStochCalc.Ito.JumpFormula.abs_markCut_le _ _ _ _ _).trans (LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le hu hc hc0 s _ _ e)
  · refine _root_.Prove2MeSourceProof.h_7ac4f497a1ed78b320395909
      (a := fun i ω s e => coeffs.γ s (X.X s ω) e i) (c := n * c)
      (fun i => S.γ_meas i) (fun ω s e => ?_) T (fun i => S.γ_sq i T hT)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hc0)
      (Finset.sum_nonneg fun i _ => abs_nonneg _))]
end Mixed

end LevyStochCalc.Ito.JumpFormula


