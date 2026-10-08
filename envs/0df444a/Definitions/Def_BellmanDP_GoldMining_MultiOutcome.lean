-- Prove2me | Definitions.Def_BellmanDP_GoldMining_MultiOutcome
-- name    : BellmanDP_GoldMining_MultiOutcome
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T14:59:31.31872+00:00
-- url     : https://prove2.me/theorems/155b79ac-b428-415a-84b8-313d732682c6
-- title:
--   Gold mining with several outcomes per use: the two-mine equation of Theorem 3 and the $n$-mine equation and decision functions $D_i(x)$ of Theorem 4
-- statement:
--   This file sets up the generalizations of the gold-mining equation in § 10 of Chapter II, where a use of the machine has $K$ possible outcomes.
--
--   1. **Two mines (Theorem 3).** Using the machine in the first mine produces outcome $k$ with probability $p_k$; it then yields the fraction $c_k$ of the gold $x$ and leaves $c'_kx$. In the second mine the data are $q_k, d_k, d'_k$. The two alternatives are
--   $$A = \sum_{k=1}^{K} p_k\bigl[c_kx + f(c'_kx,\,y)\bigr], \qquad B = \sum_{k=1}^{K} q_k\bigl[d_ky + f(x,\,d'_ky)\bigr],$$
--   and $f$ solves the equation when $f(x,y) = \max(A, B)$ for all $x, y \ge 0$.
--   2. **$n$ mines (Theorem 4).** The state is $x = (x_1,\dots,x_n)$ with all $x_i \ge 0$. The $i$-th alternative is
--   $$\Phi_i(f,x) = \sum_{k=1}^{K} p_{ik}\bigl[c_{ik}x_i + f(x_1,\dots,c'_{ik}x_i,\dots,x_n)\bigr],$$
--   in which only the $i$-th coordinate is replaced. $f$ solves (4) when $f(x) = \max_i \Phi_i(f,x)$ for all $x$ in the orthant.
--   3. The function class for the $n$-mine equation: $f$ is bounded on every box $0 \le x_i \le \bar X_i$, $i = 1,\dots,n$.
--   4. The decision functions of Theorem 4:
--   $$D_i(x) = \frac{\sum_{k=1}^{K} p_{ik}c_{ik}}{1 - \sum_{k=1}^{K} p_{ik}}\,x_i.$$
--
--   **Formalization Note** Outcomes are indexed by `Fin K` (the book writes $N$ outcomes in Theorem 3 and $K$ in Theorem 4) and mines by `Fin n`. The maximum over the mines is encoded as "every alternative is at most $f(x)$ and some alternative equals $f(x)$". The book's standing conditions ($\sum_k p_{ik} < 1$ and so on) are hypotheses of the theorems, not part of these definitions.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 10, Theorem 3, Eq. (1), p. 69; Theorem 4, Eq. (4) and the decision functions D_i(x), p. 70

import Mathlib

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, § 10, Theorem 3, Eq. (1), p. 69, choice A: with `K`
possible outcomes `k`, outcome `k` occurring with probability `p k`, yielding the fraction `c k`
of the gold `x` and leaving `c' k * x`:
`Σ_k p_k [c_k x + f(c'_k x, y)]`. -/
def optA (K : ℕ) (p c c' : Fin K → ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ k : Fin K, p k * (c k * x + f (c' k * x) y)

/-- Ch. II, Theorem 3, Eq. (1), p. 69, choice B: `Σ_k q_k [d_k y + f(x, d'_k y)]`. -/
def optB (K : ℕ) (q d d' : Fin K → ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ k : Fin K, q k * (d k * y + f x (d' k * y))

/-- Ch. II, Theorem 3, Eq. (1), p. 69: `f(x, y) = Max [A, B]` for all `x, y ≥ 0`. -/
def IsTwoMineSolution (K : ℕ) (p c c' q d d' : Fin K → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f x y = max (optA K p c c' f x y) (optB K q d d' f x y)

/-- Ch. II, Theorem 4, Eq. (4), p. 70: the `i`-th alternative of the `n`-mine equation at the state
`x = (x_1, …, x_n)`, `Σ_k p_ik [c_ik x_i + f(x_1, …, c'_ik x_i, …, x_n)]`, where only the `i`-th
coordinate is replaced (by `c'_ik x_i`). -/
def mineOption {n K : ℕ} (p c c' : Fin n → Fin K → ℝ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k : Fin K, p i k * (c i k * x i + f (Function.update x i (c' i k * x i)))

/-- Ch. II, Theorem 4, Eq. (4), p. 70: `f(x) = Max_i mineOption i` for every `x` with all
`x_i ≥ 0`: every alternative is at most `f(x)` and some alternative equals `f(x)`. -/
def IsNMineSolution {n K : ℕ} (p c c' : Fin n → Fin K → ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
    (∀ i, mineOption p c c' f x i ≤ f x) ∧ ∃ i, f x = mineOption p c c' f x i

/-- The function class for the `n`-mine equation: bounded on every box
`0 ≤ x_i ≤ X̄_i, i = 1, …, n` (the `n`-dimensional form of Ch. II, Theorem 1's class). -/
def BoundedOnBoxes {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ X : Fin n → ℝ, ∃ M : ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ X i) → |f x| ≤ M

/-- Ch. II, Theorem 4, p. 70: the decision function
`D_i(x) = (Σ_k p_ik c_ik) x_i / (1 − Σ_k p_ik)`. -/
noncomputable def decisionFunction {n K : ℕ} (p c : Fin n → Fin K → ℝ) (x : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (∑ k : Fin K, p i k * c i k) * x i / (1 - ∑ k : Fin K, p i k)

end BellmanDP.GoldMining


