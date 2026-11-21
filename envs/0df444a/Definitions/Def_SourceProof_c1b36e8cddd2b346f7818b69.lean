-- Prove2me | Definitions.Def_SourceProof_c1b36e8cddd2b346f7818b69
-- name    : SourceProof_c1b36e8cddd2b346f7818b69
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:29:54.990911+00:00
-- url     : https://prove2.me/theorems/c667d50e-bbb5-4ecf-8923-0cc5625e5039
-- title:
--   LevyStochCalc source module: SourceProof_c1b36e8cddd2b346f7818b69
-- statement:
--   The original source theorem `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` comes from the `LevyStochCalc.Ito.BigJumpDiffusion` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F001
import Definitions.Def_SourceProof_79a6cde54e31b0f9d920e0b6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating the jumps of a jump diffusion at one mark set

Restricting the jump coefficient of a jump diffusion to a measurable set of marks `A` splits it
into two coefficient bundles, and the compensated integral of an admissible integrand splits
accordingly. Subtracting the everywhere-càdlàg modification of the compensated integral over `A`
from the path leaves the *big-jump path*, which carries the drift, the diffusion and the jumps
outside `A`.

## Main definitions

* `LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.markCutγ` — the coefficient bundle with the jump
  coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.SdeData` — the filtration and admissibility data with which a jump
  diffusion satisfies its SDE.
* `LevyStochCalc.Ito.BigJump.cutJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of the jump coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.bigJumpPath` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` — the compensated integral of
  an integrand is the sum of the compensated integrals of its two mark cuts.
* `LevyStochCalc.Ito.BigJump.lintegral_sq_iSup_bigJumpPath_lt_top` — the big-jump path has
  square-integrable supremum over every bounded window.
* `LevyStochCalc.Ito.BigJump.isItoLevyProcess_bigJumpPath` — the big-jump path is an Itô–Lévy
  process whose drift and diffusion are those of the jump diffusion along its own path and whose
  jump integrand is the jump coefficient restricted to the complement of the cut.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.Setting

universe v

variable {n d : ℕ} {E : Type v}

end LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

section Split

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_c1b36e8cddd2b346f7818b69 (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {A : Set E} (hA : MeasurableSet A) (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ (markCut A φ)
            (measurable_markCut hm hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hp) hA)
            (fun T' hT' => sq_markCut hq A T' hT') T ω
          + stochasticIntegral N ℱ hℱ (markCut Aᶜ φ)
            (measurable_markCut hm hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hp) hA.compl)
            (fun T' hT' => sq_markCut hq Aᶜ T' hT') T ω := by
  rcases le_or_gt T 0 with hT | hT
  · have hzero : ∀ (ψ : Ω → ℝ → E → ℝ)
        (h1 : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
        (h2 : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
        (h3 : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ h1 h2 h3 T =ᵐ[P] 0 := fun ψ h1 h2 h3 =>
      (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ ψ h1 h2 h3 T).trans
        (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ ψ h1 h2 h3 hT)
    filter_upwards [hzero φ hm hp hq,
      hzero (LevyStochCalc.Poisson.Compensated.markCut A φ) (LevyStochCalc.Poisson.Compensated.measurable_markCut hm hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hp) hA)
        (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut hq A T' hT'),
      hzero (LevyStochCalc.Poisson.Compensated.markCut Aᶜ φ) (LevyStochCalc.Poisson.Compensated.measurable_markCut hm hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hp) hA.compl)
        (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut hq Aᶜ T' hT')] with ω h0 h1 h2
    simp [h0, h1, h2]
  · have hpt := LevyStochCalc.Ito.BigJump.markCut_add_markCut_compl (Ω := Ω) (E := E) A φ
    have hfun : (fun ω s e => LevyStochCalc.Poisson.Compensated.markCut A φ ω s e + LevyStochCalc.Poisson.Compensated.markCut Aᶜ φ ω s e) = φ := by
      funext ω s e; exact hpt ω s e
    have hma : Measurable fun p : Ω × ℝ × E =>
        LevyStochCalc.Poisson.Compensated.markCut A φ p.1 p.2.1 p.2.2 + LevyStochCalc.Poisson.Compensated.markCut Aᶜ φ p.1 p.2.1 p.2.2 :=
      (LevyStochCalc.Poisson.Compensated.measurable_markCut hm hA).add (LevyStochCalc.Poisson.Compensated.measurable_markCut hm hA.compl)
    have hpa : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        (fun ω s e => LevyStochCalc.Poisson.Compensated.markCut A φ ω s e + LevyStochCalc.Poisson.Compensated.markCut Aᶜ φ ω s e) := by
      simp only [hpt]; exact hp
    have hqa : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markCut A φ ω s e + LevyStochCalc.Poisson.Compensated.markCut Aᶜ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
      simp only [hpt]; exact hq
    have hadd := _root_.Prove2MeSourceProof.h_79a6cde54e31b0f9d920e0b6 N ℱ hℱ
      (φ₁ := LevyStochCalc.Poisson.Compensated.markCut A φ) (φ₂ := LevyStochCalc.Poisson.Compensated.markCut Aᶜ φ)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut hm hA) (LevyStochCalc.Poisson.Compensated.measurable_markCut hm hA.compl)
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hp) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hp) hA.compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut hq A T' hT') (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut hq Aᶜ T' hT')
      hma hpa hqa hT
    rw [← LevyStochCalc.Ito.BigJump.stochasticIntegral_congr_fun N ℱ hℱ hma hpa hqa hm hp hq hfun T]
    exact hadd
end Split

section Data

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-! `SdeData` is **not** derivable from `JumpDiffusion` alone: the structure's `is_solution`
field bundles the equation and the integrand admissibility but no adaptedness of the path, and
`X_prog` does not follow from them. It is supplied where a solution is built, by
`LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn` (`Ito/SdeDataOfSolvesOn.lean`). -/

end Data

section Path

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

variable (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)

end Path

section Diffusion

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end Diffusion

end LevyStochCalc.Ito.BigJump


