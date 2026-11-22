-- Prove2me | Definitions.Def_SourceProof_2afb1f68a5c9c19e7519fbb0
-- name    : SourceProof_2afb1f68a5c9c19e7519fbb0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:24:34.965435+00:00
-- url     : https://prove2.me/theorems/7792c455-9280-48cf-955a-136695ff2dbf
-- title:
--   LevyStochCalc source module: SourceProof_2afb1f68a5c9c19e7519fbb0
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_of_path` comes from the `LevyStochCalc.Ito.JumpSplittingPathDecomposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001
import Definitions.Def_SourceProof_8f0772dfba7bc0614af4bf4b
import Definitions.Def_SourceProof_aef3a69ee291c75edeeec8a2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity splitting of a path along the left limits of another

The splitting of a path into a vector Itô process and a left-limit jump sum separates into what
is read along the evaluation path, namely the coefficients and the jump sum, and what is asked of
the split path, namely the integral equation and right continuity on the nonnegative half-line,
so the two paths are free of one another. For a jump coefficient carried by a mark set of finite
intensity whose left-limit integrand along a càdlàg evaluation path has marked predictable zero
extension, this file identifies a path satisfying the integral equation with the sum of the
vector Itô process with diffusion `σ` and drift `continuousDriftLeftAt` and the left-limit jump
sum over that mark set: almost surely at a fixed nonnegative time, and almost surely at all
nonnegative times simultaneously when the split path and a modification of the Itô process are
right-continuous. The coefficients read along the path of a jump diffusion and the case of the
jump diffusion's own path follow, the càdlàg field supplying both regularity hypotheses.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}

section SplittingAt

variable (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
  (x₀ : Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Xp p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (Xp s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
    coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ
    fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hγmL hγpL hγqL in

theorem _root_.Prove2MeSourceProof.h_2afb1f68a5c9c19e7519fbb0 (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeftAt coeffs ν Xp A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i := by
  have hwin := _root_.Prove2MeSourceProof.h_aef3a69ee291c75edeeec8a2 coeffs N Xp ℱ hℱN hA hAν hpredL hγmL hγqL
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      Z t ω i = V t ω i + LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A t ω i := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine _root_.Prove2MeSourceProof.h_231d4b01442d4e78331883f1 (P := P) (Y := fun s ω => Z s ω i)
      (Z := fun s ω => V s ω i + LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A s ω i) ?_ ?_ ?_
    · intro q hq
      filter_upwards [_root_.Prove2MeSourceProof.h_8f0772dfba7bc0614af4bf4b coeffs N Xp x₀ ℱ hℱW
        hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL Z hXpcadlag hSDE hA hAν hsupp hpredL
        hμm hμq hq, hVae (q : ℝ) hq] with ω h1 h2
      show Z (q : ℝ) ω i = V (q : ℝ) ω i + LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A (q : ℝ) ω i
      rw [h1 i, h2 i]
    · filter_upwards [hZright] with ω hω t ht
      exact ((continuous_apply i).tendsto (Z t ω)).comp (hω t ht)
    · filter_upwards [hVright, hwin] with ω hVω hwω t ht
      exact (hVω t ht i).add
        (LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSumLeftAt_nhdsWithin_Ioi coeffs N Xp hA (hγmL i) (fun T => hwω T i) t)
  filter_upwards [key] with ω hω
  intro t ht i
  exact hω i t ht
end SplittingAt

section JumpDiffusionWindow

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

end JumpDiffusionWindow

section Splitting

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting


