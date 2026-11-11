-- Prove2me | Definitions.Def_EuclideanLineAvgDist_Embedding_Markov
-- name    : EuclideanLineAvgDist_Embedding_Markov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:15.775203+00:00
-- url     : https://prove2.me/theorems/89a44b40-e5e9-4252-9981-b8add356c247
-- title:
--   Gaussian-indexed symmetric transition matrices and reversible Markov chains
-- statement:
--   Two kinds of Markov transitions used in Section 2 of the paper.
--
--   **Gaussian-indexed transitions (Lemma 2.1).** Let $X\subset\mathbb R^k$ be a finite set of size $n$. A family $(K_g)_{g\in\mathbb R^k}$ of $X\times X$ matrices is admissible if every $K_g$ is symmetric, has nonnegative entries and row sums equal to $1$, and every entry $g\mapsto K_g(x,y)$ is a Borel measurable function of $g$. Sample $\gamma\sim N(0,I_k)$ and $x_0\sim\mathrm{Unif}(X)$ independently, then $x_1\sim K_\gamma(x_0,\cdot)$; the triple $(\gamma,x_0,x_1)$ has law $N(0,I_k)(dg)\cdot\frac1n\cdot K_g(x,y)$. Accordingly
--   $$\mathbb E|\langle\gamma,x_1-x_0\rangle|=\int \frac1n\sum_{x,y\in X}K_g(x,y)\,|\langle g,y-x\rangle|\,dN(0,I_k)(g),$$
--   $$\mathbb E\|x_1-x_0\|_2^2=\int \frac1n\sum_{x,y\in X}K_g(x,y)\,\|y-x\|_2^2\,dN(0,I_k)(g).$$
--
--   **Reversible chains (Lemma 2.3).** Let $\Omega$ be a measurable space and $P$ a Markov (probability) transition kernel on $\Omega$. Its $i$-step kernel $P^i$ is defined by $P^0=\mathrm{id}$ and $P^{i+1}=P\circ P^i$. $P$ is **reversible** with respect to a measure $\pi$ (detailed balance) if the law $\pi(dx)P(x,dy)$ is invariant under exchanging $x$ and $y$. For a measurable $\varphi:\Omega\to\mathbb R^k$ and a law $\mu$ of a pair $(x,y)$, the mean squared displacement is
--   $$\mathbb E_\mu\|\varphi(y)-\varphi(x)\|_2^2\in[0,\infty],$$
--   an extended nonnegative integral that may be $+\infty$. For a chain started at $x_0\sim\pi$, the pair $(x_0,x_i)$ has law $\pi(dx)P^i(x,dy)$.
--
--   **Formalization Note** The measurability of $g\mapsto K_g(x,y)$ is the convention that makes "sample $x_1$ from $K_\gamma(x_0,\cdot)$" a random variable. With it, and since $0\le K_g\le 1$, both Gaussian expectations are integrals of integrable functions, so no default value of the Bochner integral is involved.
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 5, Lemma 2.1 (K_g, sampling of γ, x₀, x₁), p. 6, Lemma 2.3 (reversible Markov chain, stationary start), p. 14, proof of Lemma 2.1 (iterated chain)

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

noncomputable section

/-! ### Gaussian-indexed symmetric transition matrices on a finite subset of `ℝᵏ` (Lemma 2.1) -/

section GaussianTransition

variable {k : ℕ}

/-- A family `(K_g)_{g ∈ ℝᵏ}` of matrices indexed by the points of the finite set `X ⊂ ℝᵏ` such
that every `K_g` is symmetric, has nonnegative entries and row sums equal to `1`, and every entry
`g ↦ K_g(x,y)` is a (Borel) measurable function of `g`, so that `x₁ ∼ K_γ(x₀,·)` can be sampled
for a Gaussian `γ`. -/
def IsGaussianTransitionFamily (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ) : Prop :=
  (∀ g x y, K g x y = K g y x) ∧ (∀ g x y, 0 ≤ K g x y) ∧ (∀ g x, ∑ y, K g x y = 1) ∧
    (∀ x y, Measurable fun g => K g x y)

/-- `E |⟨γ, x₁ - x₀⟩|` for `γ ∼ N(0, I_k)`, `x₀ ∼ Unif(X)` independent of `γ`, and
`x₁ ∼ K_γ(x₀, ·)`; i.e. the expectation under the joint law
`N(0,I_k)(dg) · (1/n) · K_g(x,y)` of `(γ, x₀, x₁)`. -/
def projectionMean (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ) : ℝ :=
  ∫ g, (1 / (X.card : ℝ)) * ∑ x : X, ∑ y : X,
      K g x y * |inner ℝ g ((y : Eucl k) - (x : Eucl k))| ∂(stdGaussian (Eucl k))

/-- `E ‖x₁ - x₀‖₂²` under the same joint law as `projectionMean`. -/
def squaredStepMean (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ) : ℝ :=
  ∫ g, (1 / (X.card : ℝ)) * ∑ x : X, ∑ y : X,
      K g x y * ‖(y : Eucl k) - (x : Eucl k)‖ ^ 2 ∂(stdGaussian (Eucl k))

end GaussianTransition

/-! ### Markov chains on a general measurable state space (Lemma 2.3) -/

section MarkovChain

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `i`-step transition kernel `Pⁱ` of a transition kernel `P` (`P⁰` is the identity). -/
def kernelIter (P : Kernel Ω Ω) : ℕ → Kernel Ω Ω
  | 0 => Kernel.id
  | i + 1 => P ∘ₖ kernelIter P i

/-- Detailed balance (reversibility) of the transition kernel `P` with respect to the measure `π`:
the law `π(dx) P(x,dy)` of `(x₀, x₁)` is invariant under exchanging the two coordinates. -/
def IsReversible (π : Measure Ω) (P : Kernel Ω Ω) : Prop :=
  (π ⊗ₘ P).map Prod.swap = π ⊗ₘ P

/-- `E ‖φ(y) - φ(x)‖₂²` for `(x, y)` distributed according to `μ`, as an extended nonnegative
(possibly infinite) integral; `φ` places the states in `ℝᵏ`. -/
def sqDisplacement {k : ℕ} (φ : Ω → Eucl k) (μ : Measure (Ω × Ω)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (‖φ p.2 - φ p.1‖ ^ 2) ∂μ

end MarkovChain

end

end EuclideanLineAvgDist.Embedding


