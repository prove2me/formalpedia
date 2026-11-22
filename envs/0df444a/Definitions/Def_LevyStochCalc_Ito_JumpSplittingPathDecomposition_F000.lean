-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000
-- name    : LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:29:25.770095+00:00
-- url     : https://prove2.me/theorems/5506867a-d779-4ae1-9c4f-4f804a491e92
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSplittingPathDecomposition
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSplittingPathDecomposition. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001
import Definitions.Def_SourceProof_2afb1f68a5c9c19e7519fbb0
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

end SplittingAt

section JumpDiffusionWindow

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left-limit jump coefficient along the path of a jump diffusion is almost surely
integrable against the random measure over every bounded window of the mark set. -/
theorem ae_forall_integrableOn_windowLeft (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hγmL : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) :=
  _root_.Prove2MeSourceProof.h_aef3a69ee291c75edeeec8a2 coeffs N X.X ℱ hℱN hA hAν hpredL hγmL hγqL
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

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation, along the path of
a jump diffusion.** -/
theorem eq_vectorItoProcess_add_jumpSumLeft_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeft X A) t ω i
          + jumpSumLeft X A t ω i :=
  _root_.Prove2MeSourceProof.h_8f0772dfba7bc0614af4bf4b coeffs N X.X x₀ ℱ hℱW hσm hσp hσq hℱN
    hγm hγp hγq hγmL hγpL hγqL Z X.cadlag_paths hSDE hA hAν hsupp hpredL hμm hμq ht
include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation, at all
nonnegative times, along the path of a jump diffusion.** -/
theorem ae_forall_eq_add_jumpSumLeft_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeft X A t ω i :=
  _root_.Prove2MeSourceProof.h_2afb1f68a5c9c19e7519fbb0 coeffs N X.X x₀ ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq
    hγmL hγpL hγqL Z X.cadlag_paths hZright hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright
include hγmL hγpL hγqL in
/-- **The finite-activity splitting along the left limits at all nonnegative times.** The case of
the jump diffusion's own path, whose right continuity is carried by the càdlàg field. -/
theorem ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion
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
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i :=
  ae_forall_eq_add_jumpSumLeft_of_path X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL
    X.X (by filter_upwards [X.cadlag_paths] with ω hω t ht using (hω t ht).1)
    hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright
include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a jump diffusion along the left limits of its path.** If
the jump coefficient is carried by a mark set of finite intensity and the zero extension of its
left-limit integrand along the path is marked predictable, then at every nonnegative time the
path is almost surely the sum of the vector Itô process with diffusion `σ` and drift
`continuousDriftLeft`, and the left-limit jump sum over that mark set. -/
theorem eq_vectorItoProcess_add_jumpSumLeft
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
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeft X A) t ω i
          + jumpSumLeft X A t ω i :=
  eq_vectorItoProcess_add_jumpSumLeft_of_path X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL
    hγqL X.X hSDE hA hAν hsupp hpredL hμm hμq ht
include hγmL hγpL hγqL in
/-- **The finite-activity splitting along the left limits at all nonnegative times.** If the jump
coefficient is carried by a mark set of finite intensity, the zero extension of its left-limit
integrand along the path is marked predictable and `V` is a modification of the vector Itô
process with diffusion `σ` and drift `continuousDriftLeft` whose paths are right-continuous, then
almost surely the path is, at every nonnegative time, the sum of `V` and the left-limit jump sum
over that mark set. -/
theorem ae_forall_eq_add_jumpSumLeft
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
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i :=
  ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL
    hγqL hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright
end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting


