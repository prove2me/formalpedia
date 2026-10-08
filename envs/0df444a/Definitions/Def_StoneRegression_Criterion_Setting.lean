-- Prove2me | Definitions.Def_StoneRegression_Criterion_Setting
-- name    : StoneRegression_Criterion_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:12.803278+00:00
-- url     : https://prove2.me/theorems/c4424614-07bc-4960-9ee5-4bc43b9d3b85
-- title:
--   pp. 596–598 — weight sequences, conditions (1)–(5), the i.i.d. data sequence and consistency
-- statement:
--   This file fixes the setting of C. J. Stone's *Consistent nonparametric regression* (1977).
--
--   **Data.** Let $\mu$ be a probability measure on $\mathbb R^d$ and let $X, X_1, X_2, \dots$ be i.i.d. with law $\mu$. Their joint law is the product measure $P_X = \mu^{\otimes\mathbb N}$ on sequences $\omega = (\omega_0, \omega_1, \dots)$, where $\omega_0 = X$ and $\omega_i = X_i$. When responses are present, $Y$ is real valued and the pairs $(X,Y), (X_1,Y_1), (X_2,Y_2),\dots$ are i.i.d.; their common law is $\mu\otimes\kappa$, where $\kappa$ is a Markov kernel from $\mathbb R^d$ to $\mathbb R$ (the conditional law of $Y$ given $X$), and their joint law is $P_{\mu,\kappa} = (\mu\otimes\kappa)^{\otimes\mathbb N}$. The **regression function** is $E(Y\mid X=x) = \int y\,\kappa(x,dy)$.
--
--   **Weights.** A sequence of weights $\{W_n\}$ assigns to each $n$ and each point $(x, x_1,\dots,x_n)$ numbers $W_{ni}(x) = W_{ni}(x, x_1,\dots,x_n)$, $1\le i\le n$. The weights are *nonnegative* if $W_n\ge 0$, and *probability weights* if moreover $\sum_i W_{ni}(x) = 1$ for $n\ge1$. The estimator of $E(Y\mid X)$ is
--   $$\hat E_n(Y\mid X) = \sum_{i=1}^n W_{ni}(X)\,Y_i .$$
--
--   **Consistency.** $\{W_n\}$ is *consistent* if for every conditional law $\kappa$ of $Y$ given $X$ and every $r>1$ with $E|Y|^r<\infty$,
--   $$\lim_{n\to\infty} E\,\big|\hat E_n(Y\mid X) - E(Y\mid X)\big|^r = 0 .$$
--
--   **Conditions (1)–(5).** For a constant $C$, condition (1) says $E\sum_i |W_{ni}(X)|\,f(X_i) \le C\,Ef(X)$ for every nonnegative Borel $f$ and every $n\ge1$. For a constant $D$, condition (2) says $P\big(\sum_i |W_{ni}(X)|\le D\big) = 1$ for every $n\ge1$. Condition (3): $\sum_i |W_{ni}(X)|\,I_{\{\|X_i - X\|>a\}}\to0$ in probability for every $a>0$. Condition (4): $\sum_i W_{ni}(X)\to1$ in probability. Condition (5): $\max_i |W_{ni}(X)|\to0$ in probability.
--
--   These are the objects in which Theorem 1 (the consistency criterion), Theorem 2 (nearest-neighbor weights) and Theorem 3 (conditional quantiles), with their supporting corollaries and propositions, are stated; the three missions of the series share this one file.
--
--   **Formalization Note.** Sample indices are $0$-based ($i : \mathrm{Fin}\,n$ stands for the paper's $i+1$). Each $W_n$ is assumed jointly Borel in $(x, x_1,\dots,x_n)$ (`MeasurableWeights`), an assumption the paper leaves implicit. "Whenever $(X,Y),(X_1,Y_1),\dots$ are i.i.d." is encoded by quantifying over all Markov kernels $\kappa$; every joint law with first marginal $\mu$ disintegrates in this way on $\mathbb R^d\times\mathbb R$. The p. 596 assumption that the probability space carries independent standard normal variables independent of the $X$'s is supplied by the kernel $\kappa\equiv N(0,1)$. All expectations of nonnegative quantities, including $E|Y|^r$ and $E|\hat E_n - E(Y\mid X)|^r$, are lower Lebesgue integrals in $[0,\infty]$, so an infinite expectation is never silently replaced by $0$. Convergence in probability is Mathlib's `TendstoInMeasure`. The maximum in (5) is a supremum over the finite index set (equal to $0$ when $n = 0$). Consistency uses the printed $r>1$ (p. 597). The proof of Theorem 1 establishes the stronger $L^r$ conclusion also at $r=1$ (p. 611); this does not change the defined predicate. The regression function is a Bochner integral, so it is $0$ at any $x$ where $\kappa(x,\cdot)$ has no finite mean; whenever $E|Y|^r<\infty$ with $r>1$ this happens only on a $\mu$-null set, so $x\mapsto\int y\,\kappa(x,dy)$ is a version of $E(Y\mid X=x)$.
-- source:
--   Stone (1977), Ann. Statist. 5, §1 pp. 596–597 (weights, estimator, consistency); §2 p. 598 (conditions (1)–(5) of Theorem 1)

import Mathlib

namespace StoneRegression.Criterion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- A sequence of weight functions: `W n x xs i = W_{n,i+1}(x, x₁, …, xₙ)` (p. 596), with the sample
`xs i = x_{i+1}` 0-based. Weights with index `> n` are `0` in the paper and do not exist here. -/
abbrev WeightSeq (d : ℕ) : Type :=
  (n : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin n → EuclideanSpace ℝ (Fin d)) → Fin n → ℝ

/-- Each `W n` is jointly Borel in `(x, x₁, …, xₙ)` (standing assumption, disclosed). -/
def MeasurableWeights {d : ℕ} (W : WeightSeq d) : Prop :=
  ∀ n, Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n p.1 p.2)

/-- `W_n ≥ 0` for every `n` (p. 596, "nonnegative"). -/
def Nonneg {d : ℕ} (W : WeightSeq d) : Prop := ∀ n x xs i, 0 ≤ W n x xs i

/-- Probability weights (p. 596): nonnegative and `∑ᵢ W_{ni}(x) = 1`, for every `n ≥ 1`. -/
def ProbWeights {d : ℕ} (W : WeightSeq d) : Prop :=
  ∀ n, 1 ≤ n → ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1

/-- The law of the i.i.d. sequence `X, X₁, X₂, …` on `ℕ → ℝᵈ`: coordinate `0` is `X`, coordinate `i+1` is
`X_{i+1}` (p. 596). -/
noncomputable def xLaw {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    Measure (ℕ → EuclideanSpace ℝ (Fin d)) :=
  Measure.infinitePi (fun _ : ℕ => μ)

/-- The first `n` sample points `(X₁, …, Xₙ)` of a path, 0-based. -/
def sample {α : Type*} (ω : ℕ → α) (n : ℕ) : Fin n → α := fun i => ω (i.val + 1)

/-- `W_{n,i+1}(X)` on the path `ω` of the `X`-sequence. -/
def wAt {d : ℕ} (W : WeightSeq d) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℝ :=
  W n (ω 0) (sample ω n) i

/-- The law of the i.i.d. pairs `(X, Y), (X₁, Y₁), …` when `X ~ μ` and `κ` is the conditional law of `Y`
given `X`. -/
noncomputable def pairLaw {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    Measure (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => μ ⊗ₘ κ)

/-- The estimate `Ê_n(Y | X) = ∑ᵢ W_{ni}(X) Yᵢ` (p. 596) on a path of pairs. -/
def estimate {d : ℕ} (W : WeightSeq d) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i * (ω (i.val + 1)).2

/-- The regression function `E(Y | X = x) = ∫ y κ(x, dy)`. -/
noncomputable def regFn {d : ℕ} (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, y ∂(κ x)

/-- Consistency (p. 597): for every conditional law `κ` of `Y` given `X` and every `r > 1` with
`E|Y|ʳ < ∞`, `E|Ê_n(Y|X) − E(Y|X)|ʳ → 0`. -/
def IsConsistent {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) : Prop :=
  ∀ (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] (r : ℝ), 1 < r →
    ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞ →
    Tendsto (fun n => ∫⁻ ω, ‖estimate W n ω - regFn κ (ω 0).1‖ₑ ^ r ∂(pairLaw μ κ)) atTop (𝓝 0)

/-- Condition (1) with constant `C` (p. 598): `E ∑ᵢ |W_{ni}(X)| f(Xᵢ) ≤ C·E f(X)` for every nonnegative
Borel `f` and every `n ≥ 1`. -/
def Cond1 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d)
    (C : ℝ≥0) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∀ n, 1 ≤ n →
    ∫⁻ ω, ∑ i : Fin n, ‖wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) ≤ C * ∫⁻ x, f x ∂μ

/-- Condition (2) with constant `D` (p. 598): `P(∑ᵢ |W_{ni}(X)| ≤ D) = 1` for every `n ≥ 1`. -/
def Cond2 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d)
    (D : ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ᵐ ω ∂(xLaw μ), ∑ i : Fin n, |wAt W n ω i| ≤ D

/-- Condition (3) (p. 598): `∑ᵢ |W_{ni}(X)| I{‖Xᵢ − X‖ > a} → 0` in probability for every `a > 0`. -/
def Cond3 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d) : Prop :=
  ∀ a : ℝ, 0 < a → TendstoInMeasure (xLaw μ)
    (fun n ω => ∑ i : Fin n, |wAt W n ω i| * (if a < ‖ω (i.val + 1) - ω 0‖ then 1 else 0)) atTop (fun _ => 0)

/-- Condition (4) (p. 598): `∑ᵢ W_{ni}(X) → 1` in probability. -/
def Cond4 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d) : Prop :=
  TendstoInMeasure (xLaw μ) (fun n ω => ∑ i : Fin n, wAt W n ω i) atTop (fun _ => 1)

/-- Condition (5) (p. 598): `maxᵢ |W_{ni}(X)| → 0` in probability. The `⨆` over `Fin n` is the true maximum
for `n ≥ 1` (finite, nonempty) and `0` for `n = 0`. -/
def Cond5 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (W : WeightSeq d) : Prop :=
  TendstoInMeasure (xLaw μ) (fun n ω => ⨆ i : Fin n, |wAt W n ω i|) atTop (fun _ => 0)

end StoneRegression.Criterion


