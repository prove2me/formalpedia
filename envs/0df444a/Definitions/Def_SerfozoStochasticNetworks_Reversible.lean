-- Prove2me | Definitions.Def_SerfozoStochasticNetworks_Reversible
-- name    : SerfozoStochasticNetworks_Reversible
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-19T02:49:23.558963+00:00
-- url     : https://prove2.me/theorems/2878b457-f126-4521-841c-d83f712ab37a
-- title:
--   Reversibility of a rate function: detailed balance, paths, rate ratios, Kolmogorov's criterion and the communication graph
-- statement:
--   The apparatus of chapter 2 of Serfozo, *Introduction to Stochastic Networks*, for a real-valued
--   rate function $q$ on an arbitrary state space $\mathbb E$.
--
--   **Detailed balance.** $\pi$ satisfies the detailed balance equations for $q$ when
--   $\pi(x)q(x,y)=\pi(y)q(y,x)$ for all $x,y$. The rate function is **reversible** when some
--   strictly positive $\pi$ does.
--
--   **Two-way communication.** $q(x,y)>0$ if and only if $q(y,x)>0$.
--
--   **Paths.** A path of length $n$ is a sequence $x_0,\dots,x_n$ with $q(x_{i-1},x_i)>0$ for every
--   $i$. Along a path one forms the forward product $\prod_i q(x_{i-1},x_i)$, the backward product
--   $\prod_i q(x_i,x_{i-1})$, and the product of rate ratios
--   $\prod_i q(x_{i-1},x_i)/q(x_i,x_{i-1})$.
--
--   **Kolmogorov's criterion.** For every sequence $x_0,\dots,x_n$ with $x_n=x_0$, the forward and
--   backward products agree.
--
--   **Ratio invariance.** For any two paths with the same first state and the same last state, the
--   products of rate ratios agree.
--
--   **Irreducibility.** Every state is reachable from every other along a path.
--
--   **Invariant measure.** $\pi(x)\sum_y q(x,y)=\sum_y\pi(y)q(y,x)$ for every $x$, the sums being
--   unconditional sums over the state space.
--
--   **Communication graph.** The simple graph on $\mathbb E$ joining distinct $x,y$ when
--   $q(x,y)\ne0$ or $q(y,x)\ne0$.
--
--   **Birth–death process.** On the non-negative integers, $q(x,x+1)=\lambda(x)$,
--   $q(x+1,x)=\mu(x+1)$ and $q=0$ otherwise; with the measure
--   $\pi(x)=\prod_{n=0}^{x-1}\lambda(n)/\mu(n+1)$, normalized so that $\pi(0)=1$.
--
--   **Formalization Note** Nothing here requires a stochastic process, a measure space, or even a
--   countable state space: reversibility is treated as the algebraic property of the rates that the
--   book says it is, so the same definitions serve a discrete-time chain with $q$ read as transition
--   probabilities.
--
--   A path of length zero is a single state, and its three products are empty, hence equal to $1$.
--
--   Kolmogorov's criterion is stated for arbitrary closed sequences rather than for closed paths,
--   which is how the book states it; under two-way communication the two readings coincide, since a
--   vanishing rate forces its reverse to vanish and both products to be zero.
--
--   Division by zero is zero in the reals, so a rate ratio at a pair with no reverse transition is
--   $0$; along a path this never arises, since two-way communication makes the denominator
--   positive.
--
--   The invariant-measure condition uses unconditional sums, which are $0$ when the family is not
--   summable; the statements that use it carry explicit summability hypotheses.
-- source:
--   Serfozo, Introduction to Stochastic Networks, Springer 1999, chapter 2, pp. 44-50 (PDF pp. 57-63): the detailed balance equations (2.1) p. 45, "pi(x) q(x, y) = pi(y) q(y, x), x, y in E"; the two-way communication property p. 45; the communication graph p. 46, "an undirected graph whose set of vertices is the state space E and there is an edge linking a pair x, y if either q(x, y) or q(y, x) is not 0"; paths and the ratio rho(x, y) = q(x, y)/q(y, x) p. 50, "We say that a sequence of states x0, x1, ..., xn in E is a path if q(x_{i-1}, x_i) > 0, i = 1, ..., n"; Kolmogorov's criterion and expression (2.9) in Theorem 2.8 p. 50; and the birth-death rates and measure (2.3) of Example 2.1, pp. 45-46. sha256 919f20ee082ec19faa80bdd923a5529fce9c4b6d3264fdb77c5efa64256bb463

import Mathlib

namespace SerfozoStochasticNetworks

variable {E : Type*}

/-- The **detailed balance** equations `π(x) q(x,y) = π(y) q(y,x)`.
Serfozo, *Introduction to Stochastic Networks*, (2.1). -/
def DetailedBalance (q : E → E → ℝ) (π : E → ℝ) : Prop := ∀ x y, π x * q x y = π y * q y x

/-- A transition rate function is **reversible** when some positive measure satisfies its detailed
balance equations. Serfozo, Definition 1.4 and section 2.1. -/
def IsReversible (q : E → E → ℝ) : Prop := ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ DetailedBalance q π

/-- The **two-way communication** property: `q(x,y)` and `q(y,x)` are positive together.
Serfozo, section 2.1. -/
def TwoWay (q : E → E → ℝ) : Prop := ∀ x y, 0 < q x y ↔ 0 < q y x

/-- `x₀, …, x_n` is a **path** when every consecutive transition has positive rate.
Serfozo, section 2.3. -/
def IsPath (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : Prop :=
  ∀ i : Fin n, 0 < q (p i.castSucc) (p i.succ)

/-- The product of the rates along a path, read forwards. -/
def pathRate (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : ℝ :=
  ∏ i : Fin n, q (p i.castSucc) (p i.succ)

/-- The product of the rates along a path, read backwards. -/
def pathRateRev (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : ℝ :=
  ∏ i : Fin n, q (p i.succ) (p i.castSucc)

/-- The product of the rate ratios `ρ(x,y) = q(x,y)/q(y,x)` along a path; the right-hand side of
Serfozo's expression (2.9). -/
noncomputable def pathRatio (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : ℝ :=
  ∏ i : Fin n, q (p i.castSucc) (p i.succ) / q (p i.succ) (p i.castSucc)

/-- **Kolmogorov's criterion**: around every closed path the forward and backward products of the
rates agree. Serfozo, Theorem 2.8 (ii). -/
def KolmogorovCriterion (q : E → E → ℝ) : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → E), p 0 = p (Fin.last n) → pathRate q p = pathRateRev q p

/-- The ratio form of Kolmogorov's criterion: the product of rate ratios along a path depends on
the path only through its endpoints. Serfozo, Theorem 2.8 (iii). -/
def RatioInvariance (q : E → E → ℝ) : Prop :=
  ∀ (n n' : ℕ) (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E), IsPath q p → IsPath q p' →
    p 0 = p' 0 → p (Fin.last n) = p' (Fin.last n') → pathRatio q p = pathRatio q p'

/-- Irreducibility: every state is reachable from every other along a path. -/
def IsIrreducible (q : E → E → ℝ) : Prop :=
  ∀ x y : E, ∃ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p ∧ p 0 = x ∧ p (Fin.last n) = y

/-- `π` is an **invariant measure** of `q`: the total flow out of each state balances the flow in.
Serfozo, section 2.1. -/
def IsInvariant (q : E → E → ℝ) (π : E → ℝ) : Prop :=
  ∀ x, π x * ∑' y, q x y = ∑' y, π y * q y x

/-- The **communication graph** of `q`: an undirected graph on the state space with an edge
between distinct `x` and `y` when either rate between them is non-zero. Serfozo, section 2.1. -/
def commGraph (q : E → E → ℝ) : SimpleGraph E :=
  SimpleGraph.fromRel fun x y => q x y ≠ 0

/-- The transition rates of a **birth-death process** on `ℕ`: arrivals at rate `lam x` and
departures at rate `mu x`. Serfozo, Example 2.1. -/
def birthDeathRate (lam mu : ℕ → ℝ) (x y : ℕ) : ℝ :=
  if y = x + 1 then lam x else if x = y + 1 then mu x else 0

/-- The measure `π(x) = ∏_{n=1}^{x} λ(n-1)/μ(n)` of Serfozo (2.3), normalized so `π(0) = 1`. -/
noncomputable def birthDeathMeasure (lam mu : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∏ n ∈ Finset.range x, lam n / mu (n + 1)

end SerfozoStochasticNetworks


