-- Prove2me | Definitions.Def_HighDimStat_Localization_Core
-- name    : HighDimStat_Localization_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:31:12.114971+00:00
-- url     : https://prove2.me/theorems/9d1d731c-3546-4642-bf7d-0fe058dd0529
-- title:
--   Population/empirical L2-norms and the localized population Rademacher complexity
-- statement:
--   This file collects Chapter 14's core vocabulary for relating population and empirical
--   $L^2$-norms over a function class $F$ on a covariate space $X$.
--
--   - **`popNormSq μ f`** / **`popNorm μ f`**: the population $L^2(P)$ squared norm
--     $\|f\|_2^2:=\int_X f(x)^2\,P(dx)$ and its square root (Eq. (14.1)).
--   - **`empiricalNormSq xs f`** / **`empiricalNorm xs f`**: the empirical $L^2(P_n)$ squared
--     norm $\|f\|_n^2:=\frac1n\sum_{i=1}^n f(x_i)^2$ and its square root (Eq. (14.2)).
--   - **`IsStarShapedAroundOrigin F`**: $f\in F,\ \alpha\in[0,1]\implies\alpha f\in F$ (p. 454).
--   - **`IsUniformlyBounded F b`**: $\|f\|_\infty\le b$ for every $f\in F$ (p. 454).
--   - **`IsIIDDesignWithRademacher xs eps P μ`**: $n$ i.i.d. samples $x_1,\dots,x_n\sim P$
--     paired with $n$ i.i.d. Rademacher signs $\varepsilon_1,\dots,\varepsilon_n\in\{-1,+1\}$
--     (equiprobable), the two sequences jointly independent of each other — the randomness
--     underlying the population Rademacher complexity.
--   - **`popRademacherComplexity xs eps P μ F δ`**: the population localized Rademacher
--     complexity
--     $$
--     R_n(\delta;F):=\mathbb E_{\varepsilon,x}\Big[\sup_{f\in F,\ \|f\|_2\le\delta}
--     \Big|\tfrac1n\sum_{i=1}^n\varepsilon_if(x_i)\Big|\Big]
--     $$
--     (Eq. (14.3)), with the localization constraint `‖f‖₂ ≤ δ` at the *population* norm,
--     distinguishing it from Chapter 13's `Gn` (which localizes at the empirical norm and uses
--     Gaussian, not Rademacher, noise) and from the unlocalized Rademacher complexity of
--     Chapter 4.
--   - **`SatisfiesCriticalInequality xs eps P μ F b δ`**: $\delta>0$ and
--     $R_n(\delta;F)\le\delta^2/b$ — the population critical inequality (14.4).
--
--   **Formalization Note** The supremum defining $R_n$ is taken over the subtype of the
--   radius-$\delta$ population-norm slice of $F$, well-defined (not the junk value `0`) since
--   `0 ∈ F` for any nonempty star-shaped `F` (taking `α = 0`). Unlike Chapter 13's `Gn`, the
--   expectation here integrates out both the noise `ε` and the samples `x` jointly, since this
--   chapter (p. 454) explicitly treats the samples as random throughout, not fixed design
--   points.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 453-455 (PDF pp. 473-475), Eqs. (14.1), (14.2), (14.3), (14.4)

import Mathlib

namespace HighDimStat.Localization

open MeasureTheory ProbabilityTheory

/-- The population `L²(P)`-squared-norm `‖f‖₂²` (Eq. (14.1), p. 453). -/
noncomputable def popNormSq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂μ

/-- The population `L²(P)`-norm `‖f‖₂`. -/
noncomputable def popNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : ℝ :=
  Real.sqrt (popNormSq μ f)

/-- The empirical `L²(Pₙ)`-squared-norm `‖f‖ₙ²` (Eq. (14.2), p. 453). -/
noncomputable def empiricalNormSq {X : Type*} {n : ℕ} (xs : Fin n → X) (f : X → ℝ) : ℝ :=
  (∑ i, (f (xs i)) ^ 2) / n

/-- The empirical `L²(Pₙ)`-norm `‖f‖ₙ`. -/
noncomputable def empiricalNorm {X : Type*} {n : ℕ} (xs : Fin n → X) (f : X → ℝ) : ℝ :=
  Real.sqrt (empiricalNormSq xs f)

/-- `F` is star-shaped around the origin (p. 454): for any `f ∈ F` and `α ∈ [0,1]`, `αf ∈ F`. -/
def IsStarShapedAroundOrigin {X : Type*} (F : Set (X → ℝ)) : Prop :=
  ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, (fun z => α * f z) ∈ F

/-- `F` is `b`-uniformly bounded (p. 454): `‖f‖∞ ≤ b` for every `f ∈ F`. -/
def IsUniformlyBounded {X : Type*} (F : Set (X → ℝ)) (b : ℝ) : Prop :=
  ∀ f ∈ F, ∀ x, |f x| ≤ b

/-- `n` i.i.d. samples `xs : Fin n → Ω → X` from `μ`, paired with `n` i.i.d. Rademacher
variates `eps : Fin n → Ω → ℝ` (values in `{-1,+1}` equiprobably), the two sequences jointly
independent of one another — the randomness underlying the population localized Rademacher
complexity (Eq. (14.3), p. 454). -/
def IsIIDDesignWithRademacher {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {n : ℕ}
    (xs : Fin n → Ω → X) (eps : Fin n → Ω → ℝ) (P : Measure Ω) (μ : Measure X) : Prop :=
  (∀ i, Measurable (xs i)) ∧ iIndepFun xs P ∧ (∀ i, Measure.map (xs i) P = μ) ∧
    (∀ i, Measurable (eps i)) ∧ iIndepFun eps P ∧
    (∀ i, (∀ ω, eps i ω = 1 ∨ eps i ω = -1) ∧ P.real {ω | eps i ω = 1} = 1 / 2) ∧
    IndepFun (fun ω i => xs i ω) (fun ω i => eps i ω) P

/-- The population localized Rademacher complexity `Rₙ(δ; F)` (Eq. (14.3), p. 454): the joint
expectation, over both the Rademacher signs `ε` and the samples `x`, of the supremum over the
population-radius-`δ` slice `{f ∈ F | ‖f‖₂ ≤ δ}` of the absolute empirical Rademacher process
`|(1/n)Σᵢεᵢf(xᵢ)|`. -/
noncomputable def popRademacherComplexity {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {n : ℕ}
    (xs : Fin n → Ω → X) (eps : Fin n → Ω → ℝ) (P : Measure Ω) (μ : Measure X)
    (F : Set (X → ℝ)) (δ : ℝ) : ℝ :=
  ∫ ω, ⨆ f : {f : X → ℝ // f ∈ F ∧ popNorm μ f ≤ δ},
      |(∑ i, eps i ω * f.1 (xs i ω)) / n| ∂P

/-- `δ` satisfies the (population) critical inequality (14.4): `Rₙ(δ;F) ≤ δ²/b`, `δ > 0`. -/
def SatisfiesCriticalInequality {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {n : ℕ}
    (xs : Fin n → Ω → X)
    (eps : Fin n → Ω → ℝ) (P : Measure Ω) (μ : Measure X) (F : Set (X → ℝ)) (b δ : ℝ) : Prop :=
  0 < δ ∧ popRademacherComplexity xs eps P μ F δ ≤ δ ^ 2 / b

end HighDimStat.Localization


