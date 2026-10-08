-- Prove2me | Definitions.Def_BellmanDP_ExistUnique_TypeThree
-- name    : BellmanDP_ExistUnique_TypeThree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:28:50.067268+00:00
-- url     : https://prove2.me/theorems/13ab9b2c-5536-49d0-adc8-7544677606ec
-- title:
--   The equation of the third type $f(p)=\min[1+\sum_k p_kf(x_k),\ \min_l(1+f(T_lp))]$ on the simplex
-- statement:
--   This file sets up the equation of Chapter IV, § 8. A system is in one of $n+1$ states $0, 1, \dots, n$, and $p = (p_0, \dots, p_n)$ with $p_i \ge 0$, $\sum_{i=0}^n p_i = 1$ is the current probability distribution over them; $x_k$ is the vertex of the simplex with a $1$ in place $k$. Each operation costs one unit of time. Operation $L$ observes the state; operation $A_l$ ($l = 1, \dots, M$) transforms $p$ into $T_l p = (p_{0l}, \dots, p_{nl})$. The goal is to reach state $0$ with certainty.
--
--   1. The simplex and its vertices $x_k$.
--   2. The hypotheses on the transformations: $M \ge 1$; each $T_l$ maps the simplex into itself with $p_{0l} \ne 1$ (Eq. (8.2)); and, for a constant $0 < c_1 < 1$ and all $p$ in the simplex, $\sum_{k=1}^n p_{kl} \le c_1$ (Theorem 5, (3)).
--   3. The equation (8.1): $f(x_0) = 0$ and, for $p \ne x_0$ in the simplex,
--   $$f(p) = \min\Big[\,1 + \sum_{k=0}^{n} p_k f(x_k),\ \min_{1 \le l \le M}\big[1 + f(T_l p)\big]\Big].$$
--   4. Boundedness of a function on the simplex.
--
--   $f(p)$ is the minimal expected time to reach state $0$ from the distribution $p$.
--
--   **Formalization Note** Distributions are functions `Fin (n+1) → ℝ` and the transformations are indexed by `Fin M`. The inner minimum is a finite infimum, which is genuine because $M \ge 1$ is part of the hypotheses. The book writes the number of states both as $N+1$ and as $n+1$; the formalization uses $n+1$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 8, Eqs. (8.1)-(8.2), p. 125; Theorem 5, condition (3), p. 126

import Mathlib

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 8, Eq. (8.2), p. 125: the probability simplex
`p = (p₀, …, pₙ)`, `pᵢ ≥ 0`, `Σ_{i=0}^n pᵢ = 1`. -/
def simplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- Eq. (8.2): the vertex `x_k = (0, …, 1, …, 0)`, the `1` in the `k`-th place. -/
def vertex (n : ℕ) (k : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  Pi.single k 1

/-- Ch. IV, § 8, Eq. (8.2) and Theorem 5, condition (3), p. 126: the transformations
`T_l p = (p_{0l}, …, p_{nl})`, `l = 1, …, M` (indexed here by `Fin M`), map the simplex into
itself with `p_{0l} ≠ 1`, and `Σ_{k=1}^n p_{kl} ≤ c₁` with `0 < c₁ < 1`, for all `p`. -/
structure TypeThreeHyp (n M : ℕ) (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (c₁ : ℝ) : Prop where
  /-- `l` runs over `1, 2, …, M`, so there is at least one transformation. -/
  M_pos : 0 < M
  /-- (8.2) `p_{il} ≥ 0`, `Σ_{i=0}^n p_{il} = 1`. -/
  mapsTo : ∀ l, ∀ p ∈ simplex n, Tr l p ∈ simplex n
  /-- (8.2) `p_{0l} ≠ 1`. -/
  zero_ne_one : ∀ l, ∀ p ∈ simplex n, Tr l p 0 ≠ 1
  /-- Theorem 5 (3): `0 < c₁`. -/
  c_pos : 0 < c₁
  /-- Theorem 5 (3): `c₁ < 1`. -/
  c_lt_one : c₁ < 1
  /-- Theorem 5 (3): `Σ_{k=1}^n p_{kl} ≤ c₁`. -/
  tail_le : ∀ l, ∀ p ∈ simplex n, ∑ k : Fin n, Tr l p k.succ ≤ c₁

/-- Ch. IV, § 8, Eq. (8.1), p. 125: `f` solves
`f(p) = Min [1 + Σ_{k=0}^n p_k f(x_k), Min_l [1 + f(T_l p)]]` for `p ≠ x₀` in the simplex, and
`f(x₀) = 0`. (`Min_l` is a finite infimum over `Fin M`, genuine when `0 < M`.) -/
def SolvesTypeThree (n M : ℕ) (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (f : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  f (vertex n 0) = 0 ∧
    ∀ p ∈ simplex n, p ≠ vertex n 0 →
      f p = min (1 + ∑ k, p k * f (vertex n k)) (⨅ l : Fin M, (1 + f (Tr l p)))

/-- A bounded function on the simplex. -/
def BoundedOnSimplex (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∃ B : ℝ, ∀ p ∈ simplex n, |f p| ≤ B

end BellmanDP.ExistUnique


