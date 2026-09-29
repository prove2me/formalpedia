-- Prove2me | Definitions.Def_RobustMeanCov_TwoPoint_TwoPointSupport
-- name    : RobustMeanCov_TwoPoint_TwoPointSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:48:13.057985+00:00
-- url     : https://prove2.me/theorems/c093638d-b057-4ad3-8472-40a877c99af4
-- title:
--   The two-point support property of a function $u:\mathbb R\to\mathbb R$ (Popescu 2007, Definition 1)
-- statement:
--   This formalizes the family $\mathcal Q$ and Definition 1 of Popescu (2007). Let $u:\mathbb R\to\mathbb R$.
--
--   1. The family $\mathcal Q$ consists of the coefficient triples $(A,B,C)$ of quadratic functions dominated by $u$:
--   $$
--   \mathcal Q=\{(A,B,C)\mid q(y)=Ay^2+By+C\le u(y)\ \ \forall y\in\mathbb R\}.
--   $$
--   2. For reals $a,b,\mu,\sigma$, a **feasible $(\mu,\sigma^2)$ distribution with support $\{a,b\}$** exists if there is $p\in(0,1)$ such that the law putting mass $p$ on $a$ and mass $1-p$ on $b$ has mean $\mu$ and variance $\sigma^2$:
--   $$
--   pa+(1-p)b=\mu,\qquad p(a-\mu)^2+(1-p)(b-\mu)^2=\sigma^2 .
--   $$
--   3. $u$ satisfies the **two-point support property with respect to $(\mu,\sigma^2)$** if there are $a<b$ and $(A,B,C)\in\mathcal Q$ whose quadratic $q$ meets $u$ at $a$ and at $b$, i.e. $q(a)=u(a)$ and $q(b)=u(b)$, and a feasible $(\mu,\sigma^2)$ distribution with support $\{a,b\}$ exists.
--   4. $u$ satisfies the **two-point support property** if it satisfies it with respect to every $(\mu,\sigma^2)$ with $\sigma>0$.
--
--   Functions with this property are those for which the worst case of $E[u(r)]$ over all laws with given mean and variance is attained, or approached, on two-point laws.
--
--   **Formalization Note** A law with support $\{a,b\}$, $a<b$, is encoded elementarily by its mass $p\in(0,1)$ on $a$; both masses are positive, so the support is exactly $\{a,b\}$. "Intersects it at two points" is read as $q(a)=u(a)$ and $q(b)=u(b)$ for some $a<b$ (at least two contact points), which is the reading under which the paper's Lemma 1 is an equivalence. The property is required for every $\sigma>0$ (as in Lemma 1, "for any $\mu$ and any $\sigma>0$"): no law with two distinct support points has variance $0$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, pp. 100–101, §3 (family 𝒬), p. 101, Definition 1; two-point laws: p. 101, proof of Proposition 2

import Mathlib

namespace RobustMeanCov.TwoPoint

/-- The family `𝒬` (Popescu 2007, pp. 100–101): coefficient triples `(A, B, C)` of quadratics
`q(y) = A y² + B y + C` with `q(y) ≤ u(y)` for every real `y`. -/
def SupportFamily (u : ℝ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {ABC | ∀ y : ℝ, ABC.1 * y ^ 2 + ABC.2.1 * y + ABC.2.2 ≤ u y}

/-- A probability law on the real line with support `{a, b}`, mean `μ` and variance `σ²` exists:
there is a mass `p ∈ (0, 1)` on `a` (and `1 - p` on `b`) giving mean `μ` and variance `σ²`. -/
def TwoPointLawExists (a b μ σ : ℝ) : Prop :=
  ∃ p ∈ Set.Ioo (0 : ℝ) 1,
    p * a + (1 - p) * b = μ ∧ p * (a - μ) ^ 2 + (1 - p) * (b - μ) ^ 2 = σ ^ 2

/-- Definition 1 (Popescu 2007, p. 101), with respect to `(μ, σ²)`: some quadratic
`q(y) = A y² + B y + C` supports `u` from below and meets it at two points `a < b`, and a law
with mean `μ`, variance `σ²` and support `{a, b}` exists. -/
def TwoPointSupportWrt (u : ℝ → ℝ) (μ σ : ℝ) : Prop :=
  ∃ a b A B C : ℝ, a < b ∧ (A, B, C) ∈ SupportFamily u ∧
    A * a ^ 2 + B * a + C = u a ∧ A * b ^ 2 + B * b + C = u b ∧
    TwoPointLawExists a b μ σ

/-- Definition 1: `u` satisfies the two-point support property if it satisfies it with respect to
every `(μ, σ²)` with `σ > 0`. -/
def TwoPointSupport (u : ℝ → ℝ) : Prop :=
  ∀ μ σ : ℝ, 0 < σ → TwoPointSupportWrt u μ σ

end RobustMeanCov.TwoPoint


