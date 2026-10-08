-- Prove2me | Definitions.Def_SolutionQuality_SRP_Setting
-- name    : SolutionQuality_SRP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:27:30.035728+00:00
-- url     : https://prove2.me/theorems/8cf55d08-8e3f-4e65-96cf-4463ed5e87fb
-- title:
--   §1–§4, pp. 1–10 — (SP), (SP_n), (A1)–(A3), optimality gap, G_n of (2), s²_n, σ²_x̂, X*, i.i.d. sample, minimizers x*_n, x²*_n, (10)
-- statement:
--   This module fixes the objects of Bayraksan and Morton's single- and two-replication procedures for assessing the quality of a candidate solution of a stochastic program.
--
--   **The stochastic program.** Let $\tilde\xi$ be a random vector with distribution $\mu$ on a measurable space $\Xi$, let $X\subseteq\mathbb R^d$ be a set of feasible decisions and let $f:\mathbb R^d\times\Xi\to\mathbb R$ be a cost function. The problem is
--   $$
--   z^* = \min_{x\in X} E f(x,\tilde\xi),\qquad E f(x,\tilde\xi)=\int_\Xi f(x,\xi)\,\mu(d\xi). \qquad\text{(SP)}
--   $$
--   The optimal set is $X^*=\{x\in X : Ef(x,\tilde\xi)\le Ef(y,\tilde\xi)\ \forall y\in X\}$, and the **optimality gap** of a candidate $\hat x$ is $\mu_{\hat x}=Ef(\hat x,\tilde\xi)-z^*$.
--
--   **Standing assumptions (A1)–(A3).**
--   1. (A1) $f(\cdot,\tilde\xi)$ is continuous on $X$, with probability one;
--   2. (A2) $E\sup_{x\in X} f^2(x,\tilde\xi)<\infty$, stated as: there is an integrable $g$ with $f(x,\xi)^2\le g(\xi)$ for all $x\in X$, for $\mu$-almost every $\xi$;
--   3. (A3) $X\neq\emptyset$ and $X$ is compact.
--
--   **Sampling.** $\tilde\xi^1,\tilde\xi^2,\dots$ are i.i.d. random vectors on a probability space $(\Omega,P)$, each distributed as $\tilde\xi$. For a sample path $s=(s_1,s_2,\dots)$ and a sample size $n$,
--   $$
--   \bar f_n(x)=\frac1n\sum_{i=1}^n f(x,s_i),\qquad z_n^*=\min_{x\in X}\bar f_n(x)\quad\text{(SP}_n\text{)},\qquad G_n(\hat x)=\bar f_n(\hat x)-z_n^* \quad (2),
--   $$
--   $$
--   s_n^2(x)=\frac{1}{n-1}\sum_{i=1}^n\Big[\big(f(\hat x,s_i)-f(x,s_i)\big)-\big(\bar f_n(\hat x)-\bar f_n(x)\big)\Big]^2,\qquad \sigma^2_{\hat x}(x)=\operatorname{var}\big[f(\hat x,\tilde\xi)-f(x,\tilde\xi)\big].
--   $$
--   A sequence $x_n^*$ of random vectors is an SAA minimizer sequence if, almost surely, $x_n^*\in X$ minimizes $\bar f_n$ over $X$ on the first sample $\tilde\xi^1,\dots,\tilde\xi^n$; the sequence $x_n^{2*}$ does the same on the second sample $\tilde\xi^{n+1},\dots,\tilde\xi^{2n}$. The averaged two-replication estimators of (10) are
--   $$
--   G_n'(\hat x)=\tfrac12\big(G_n^1(\hat x)+G_n^2(\hat x)\big),\qquad s_n'^2=\tfrac12\big(s_n^2(x_n^{1*})+s_n^2(x_n^{2*})\big),
--   $$
--   where the superscripts $1,2$ refer to the first and the second sample.
--
--   These objects are shared by every statement of the mission: the consistency results of Proposition 1 and the asymptotic validity of the SRP, I2RP and A2RP confidence intervals.
--
--   **Formalization Note.** The decision dimension is written $d$ (the paper writes $X\subseteq\mathbb R^n$ and also uses $n$ for the sample size). The sample is one infinite sequence `ξ 0, ξ 1, …` (0-based: the paper's $\tilde\xi^i$ is `ξ (i-1)`); the second sample of size $n$ is `ξ n, …, ξ (2n-1)`. Estimators are functions of a sample path, so one definition serves both samples. $z^*$ and $z_n^*$ are infima of images of $X$ (equal to the minima under (A1)–(A3)), $X^*$ is an argmin set without infima. Measurability of each $x_n^*$ is required, which makes precise "$x_n^*$ is a random vector". At $n=0,1$ the factors $1/n$ and $1/(n-1)$ are Lean's $1/0=0$; every statement using them is asymptotic.
-- source:
--   Bayraksan & Morton, Assessing Solution Quality in Stochastic Programs, preprint (January 26, 2005), pp. 1–10, (SP) p. 1, (A1)–(A3) and (SP_n) p. 2, μ_x̂ p. 3, (2) p. 4, notation of §3 p. 5, X* p. 6, I2RP step 3′ p. 9, (10) p. 10

import Mathlib

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter

/-- The decision space `ℝ^d` (the paper's `Rⁿ`; the letter `n` is the sample size here). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- Sample mean `f̄_n(x) = (1/n) Σ_{i=1}^n f(x, ξ̃ⁱ)` (p. 5) of the first `n` terms of the
sample path `s`; the paper's `ξ̃ⁱ` is `s (i - 1)`. -/
noncomputable def sampleMean (f : E d → Ξ → ℝ) (s : ℕ → Ξ) (n : ℕ) (x : E d) : ℝ :=
  (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, f x (s i)

/-- The expected cost `E f(x, ξ̃) = ∫ f(x, ξ) dμ(ξ)`, `μ` the distribution of `ξ̃` (p. 1). -/
noncomputable def expectedCost (μ : Measure Ξ) (f : E d → Ξ → ℝ) (x : E d) : ℝ :=
  ∫ s, f x s ∂μ

/-- The optimal value `z* = min_{x ∈ X} E f(x, ξ̃)` of (SP) (p. 1). -/
noncomputable def optValue (μ : Measure Ξ) (f : E d → Ξ → ℝ) (X : Set (E d)) : ℝ :=
  sInf (expectedCost μ f '' X)

/-- The set `X*` of optimal solutions of (SP) (p. 6). -/
def optSet (μ : Measure Ξ) (f : E d → Ξ → ℝ) (X : Set (E d)) : Set (E d) :=
  {x | x ∈ X ∧ ∀ y ∈ X, expectedCost μ f x ≤ expectedCost μ f y}

/-- The optimality gap `μ_x̂ = E f(x̂, ξ̃) − z*` of a candidate solution `x̂` (p. 3). -/
noncomputable def optGap (μ : Measure Ξ) (f : E d → Ξ → ℝ) (X : Set (E d)) (xhat : E d) : ℝ :=
  expectedCost μ f xhat - optValue μ f X

/-- The optimal value `z*_n = min_{x ∈ X} (1/n) Σ_{i=1}^n f(x, ξ̃ⁱ)` of (SP_n) (p. 2). -/
noncomputable def saaValue (f : E d → Ξ → ℝ) (X : Set (E d)) (s : ℕ → Ξ) (n : ℕ) : ℝ :=
  sInf ((fun x => sampleMean f s n x) '' X)

/-- The gap estimator `G_n(x̂) = f̄_n(x̂) − z*_n` of (2) (p. 4), on the sample path `s`. -/
noncomputable def gapEstimate (f : E d → Ξ → ℝ) (X : Set (E d)) (xhat : E d) (s : ℕ → Ξ)
    (n : ℕ) : ℝ :=
  sampleMean f s n xhat - saaValue f X s n

/-- The sample variance
`s²_n(x) = (1/(n−1)) Σ_{i=1}^n [(f(x̂, ξ̃ⁱ) − f(x, ξ̃ⁱ)) − (f̄_n(x̂) − f̄_n(x))]²` (p. 5). -/
noncomputable def sampleVar (f : E d → Ξ → ℝ) (xhat : E d) (s : ℕ → Ξ) (n : ℕ) (x : E d) : ℝ :=
  (1 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.range n,
    ((f xhat (s i) - f x (s i)) - (sampleMean f s n xhat - sampleMean f s n x)) ^ 2

/-- The variance `σ²_x̂(x) = var[f(x̂, ξ̃) − f(x, ξ̃)]` (p. 5). -/
noncomputable def gapVar (μ : Measure Ξ) (f : E d → Ξ → ℝ) (xhat x : E d) : ℝ :=
  variance (fun s => f xhat s - f x s) μ

/-- The standing assumptions (A1)–(A3) of the paper (p. 2):
(A1) `f(·, ξ̃)` is continuous on `X`, w.p.1;
(A2) `E sup_{x ∈ X} f²(x, ξ̃) < ∞`, stated as: `ξ ↦ sup_{x∈X} f(x, ξ)²` has an integrable
majorant `g`;
(A3) `X ≠ ∅` and `X` is compact. -/
structure Assumptions (μ : Measure Ξ) (f : E d → Ξ → ℝ) (X : Set (E d)) : Prop where
  A1 : ∀ᵐ s ∂μ, ContinuousOn (fun x => f x s) X
  A2 : ∃ g : Ξ → ℝ, Integrable g μ ∧ ∀ᵐ s ∂μ, ∀ x ∈ X, f x s ^ 2 ≤ g s
  A3 : X.Nonempty ∧ IsCompact X

/-- `ξ 0, ξ 1, ξ 2, …` (the paper's `ξ̃¹, ξ̃², …`) are i.i.d. random vectors on `(Ω, P)`,
each distributed as `ξ̃`, i.e. with law `μ`. -/
def IsIIDSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure Ξ)
    (ξ : ℕ → Ω → Ξ) : Prop :=
  (∀ i, Measurable (ξ i)) ∧ iIndepFun ξ P ∧ ∀ i, P.map (ξ i) = μ

/-- `x*_n` is a (measurable) optimal solution of (SP_n) built on the first sample
`ξ̃¹, …, ξ̃ⁿ` (the Lean `ξ 0, …, ξ (n-1)`), almost surely, for every `n`. -/
def IsSAAMinimizerSeq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : E d → Ξ → ℝ)
    (X : Set (E d)) (ξ : ℕ → Ω → Ξ) (xn : ℕ → Ω → E d) : Prop :=
  (∀ n, Measurable (xn n)) ∧
    ∀ n, ∀ᵐ ω ∂P, xn n ω ∈ X ∧
      ∀ y ∈ X, sampleMean f (fun i => ξ i ω) n (xn n ω) ≤ sampleMean f (fun i => ξ i ω) n y

/-- `x²*_n` is a (measurable) optimal solution of (SP_n) built on the second sample
`ξ̃^{n+1}, …, ξ̃^{2n}` (the Lean `ξ n, …, ξ (2n-1)`), almost surely, for every `n`
(I2RP step 3′.2, p. 9; A2RP, p. 10). -/
def IsSAAMinimizerSeq₂ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : E d → Ξ → ℝ)
    (X : Set (E d)) (ξ : ℕ → Ω → Ξ) (xn₂ : ℕ → Ω → E d) : Prop :=
  (∀ n, Measurable (xn₂ n)) ∧
    ∀ n, ∀ᵐ ω ∂P, xn₂ n ω ∈ X ∧
      ∀ y ∈ X, sampleMean f (fun i => ξ (n + i) ω) n (xn₂ n ω) ≤
        sampleMean f (fun i => ξ (n + i) ω) n y

/-- The A2RP pooled gap estimator `G′_n(x̂) = (1/2)(G¹_n(x̂) + G²_n(x̂))` of (10) (p. 10):
`G¹_n` on the first sample `ξ 0, …, ξ (n-1)`, `G²_n` on the second sample
`ξ n, …, ξ (2n-1)`. -/
noncomputable def pooledGap (f : E d → Ξ → ℝ) (X : Set (E d)) (xhat : E d) (s : ℕ → Ξ)
    (n : ℕ) : ℝ :=
  (1 / 2) * (gapEstimate f X xhat s n + gapEstimate f X xhat (fun i => s (n + i)) n)

/-- The A2RP pooled variance `s′²_n = (1/2)(s²_n(x¹*_n) + s²_n(x²*_n))` of (10) (p. 10),
each `s²_n` computed on its own sample. -/
noncomputable def pooledVar (f : E d → Ξ → ℝ) (xhat : E d) (s : ℕ → Ξ) (n : ℕ)
    (x₁ x₂ : E d) : ℝ :=
  (1 / 2) * (sampleVar f xhat s n x₁ + sampleVar f xhat (fun i => s (n + i)) n x₂)

end SolutionQuality.SRP


