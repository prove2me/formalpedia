-- Prove2me | Definitions.Def_GraphAlignment_Impossible_InfoMeasures
-- name    : GraphAlignment_Impossible_InfoMeasures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:07.896684+00:00
-- url     : https://prove2.me/theorems/4328d0dd-e0f4-4965-8e6f-0ecc98c7aa95
-- title:
--   Finite information measures — stochastic kernels, Kullback–Leibler divergence D(p‖r) and mutual information I(X; Y) (natural log)
-- statement:
--   This module fixes three general objects of finite information theory used throughout the impossibility proof of Hall and Massoulié.
--
--   1. **Stochastic kernel.** For finite types $\mathcal X,\mathcal Y$, a stochastic kernel $k:\mathcal X\to\Delta(\mathcal Y)$ is a real matrix $k(x,y)$ with $k(x,y)\ge 0$ and $\sum_{y}k(x,y)=1$ for every $x$. It models a randomized map: given $x$, the output is $y$ with probability $k(x,y)$. Deterministic maps are the kernels with $0/1$ entries.
--
--   2. **Kullback–Leibler divergence.** For real vectors $p,r$ on a finite set $\mathcal X$,
--   $$
--   D(p\,\|\,r)=\sum_{x\in\mathcal X}p(x)\log\frac{p(x)}{r(x)} ,
--   $$
--   which is the formula of p. 8 of the paper for two discrete probability distributions.
--
--   3. **Mutual information.** For a joint law $p(x,y)=\mathbb P(X=x,Y=y)$ on a finite product $\mathcal X\times\mathcal Y$, with marginals $p_X(x)=\sum_{y'}p(x,y')$ and $p_Y(y)=\sum_{x'}p(x',y)$,
--   $$
--   I(X;Y)=\sum_{x}\sum_{y}p(x,y)\log\frac{p(x,y)}{p_X(x)\,p_Y(y)} ,
--   $$
--   the divergence of the joint law from the product of its marginals.
--
--   These are the quantities $D(P\|Q)$, $I(Z;\hat X)$ and $I(\pi^*;(A,B))$ of §2.4 and §3 of the paper.
--
--   **Formalization Note** Logarithms are natural. Lean's conventions $0\cdot\log(\cdot)=0$ and $\log 0=0$ give the usual $0\log 0=0$ convention: a term with $p(x)=0$ (resp. $p(x,y)=0$) contributes nothing. When $p(x)>0$ but $r(x)=0$, Lean returns $\log(p/0)=0$ rather than $+\infty$; the theorems of this mission only apply $D$ to pairs where this does not occur, or say so. The definitions accept any real vectors; they carry the meaning above when the inputs are probability vectors.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 8, §2.4.1 (D(P||Q)); pp. 10–12, §3.1–§3.2 (I(Z; X̂), I(π*; (A, B)))

import Mathlib

namespace GraphAlignment.Impossible

/-- A stochastic (Markov) kernel between finite types, as a real matrix: `k x y` is the probability
of `y` given `x`; every entry is nonnegative and every row sums to `1`. -/
structure StochKernel (X Y : Type*) [Fintype Y] where
  /-- The transition probabilities. -/
  k : X → Y → ℝ
  /-- Entries are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ k x y
  /-- Rows sum to one. -/
  sum_one : ∀ x, ∑ y, k x y = 1

/-- Kullback–Leibler divergence `D(p ‖ r) = ∑ₓ p(x) log (p(x) / r(x))` of two real vectors on a
finite type (natural logarithm; a term with `p x = 0` contributes `0`). -/
noncomputable def kl {X : Type*} [Fintype X] (p r : X → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / r x)

/-- Mutual information `I(X; Y)` of a finite joint law `p x y = ℙ(X = x, Y = y)`:
`∑ₓ ∑ᵧ p(x,y) log (p(x,y) / (p_X(x) p_Y(y)))`, with the marginals computed from `p`
(natural logarithm; a term with `p x y = 0` contributes `0`). -/
noncomputable def mutualInfo {X Y : Type*} [Fintype X] [Fintype Y] (p : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * Real.log (p x y / ((∑ y', p x y') * (∑ x', p x' y)))

end GraphAlignment.Impossible


