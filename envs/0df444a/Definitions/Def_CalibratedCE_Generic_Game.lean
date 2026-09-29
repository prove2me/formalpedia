-- Prove2me | Definitions.Def_CalibratedCE_Generic_Game
-- name    : CalibratedCE_Generic_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:57:25.693806+00:00
-- url     : https://prove2.me/theorems/3d5437e3-01aa-4db2-b7cc-a62bb5f2924f
-- title:
--   The two-player game: probability vectors, correlated equilibria, best replies, $M_b(x)$ and $D_t(x,y)$ (Section 2–3, pp. 42–45)
-- statement:
--   This file fixes the two-player game of Foster and Vohra (1997) and the objects built on it.
--
--   "For $i = 1, 2$, denote by $S(i)$ the finite set of pure strategies of player $i$ and by $u_i(x, y) \in \mathbb{R}$ the payoff to player $i$ where $x \in S(1)$ and $y \in S(2)$. Let $m = |S(1)|$ and $n = |S(2)|$." (p. 42). Here $S(1) = \{0,\dots,m-1\}$ and $S(2) = \{0,\dots,n-1\}$, and the payoffs are two real $m\times n$ matrices $u_1, u_2$ that the players maximize.
--
--   1. A **probability vector** on a finite set $A$ is $p : A \to \mathbb{R}$ with $p(a) \ge 0$ for all $a$ and $\sum_a p(a) = 1$. A **joint distribution** is a probability vector $D$ on $S(1)\times S(2)$.
--   2. **Correlated equilibrium.** On p. 43 a correlated strategy $h=(h_1,h_2)$ is a correlated equilibrium if $E(u_1(h_1,h_2)) \ge E(u_1(\Phi(h_1),h_2))$ for all $\Phi : S(1)\to S(1)$ and $E(u_2(h_1,h_2)) \ge E(u_2(h_1,\Phi(h_2)))$ for all $\Phi : S(2)\to S(2)$. As p. 44 notes, "a CE is simply a joint distribution over $S(1)\times S(2)$ with a particular property": a joint distribution $D$ is a CE when
--   $$\sum_{x,y} D(x,y)\,u_1(\Phi(x),y) \le \sum_{x,y} D(x,y)\,u_1(x,y)\ \ \forall \Phi : S(1)\to S(1),\qquad \sum_{x,y} D(x,y)\,u_2(x,\Phi(y)) \le \sum_{x,y} D(x,y)\,u_2(x,y)\ \ \forall \Phi : S(2)\to S(2).$$
--   $\pi(G)$ denotes the set of correlated equilibria of the game $G = (u_1,u_2)$.
--   3. **Best-reply functions.** "We assume that when players select their best response (for a given forecast) they use a stationary and deterministic tie breaking rule" (p. 44). A best-reply function of player 1 is a map $R_1$ from forecasts (probability vectors over $S(2)$) to $S(1)$ such that for every probability vector $p$ and every $x'$, $\sum_y p(y)u_1(x',y) \le \sum_y p(y) u_1(R_1(p),y)$; symmetrically for player 2. It depends on the forecast only, the same in every round.
--   4. $M_b(x)$ is "the set of mixtures over $S(2)$ for which $x$ is a best response" (p. 45): the probability vectors $p$ with $\sum_y p(y)u_1(x',y) \le \sum_y p(y)u_1(x,y)$ for all $x'$.
--   5. $D_t(x,y)$ is "the fraction of times up to time $t$ that player 1 plays $x$ and player 2 plays $y$" (p. 44): for play sequences $(x_s)$, $(y_s)$,
--   $$D_t(x,y) = \frac{\#\{s < t : x_s = x,\ y_s = y\}}{t}.$$
--
--   These are the objects in which $\lambda(G) = \pi(G)$ is stated.
--
--   **Formalization Note** Strategies are `Fin m` and `Fin n`. Rounds are $0,\dots,t-1$ (the paper's $1,\dots,t$), and $D_0 = 0$ by Lean's division by zero; only limits of $D_t$ are ever used. The CE is the reduced joint-distribution form of p. 44 (finite probability space $\Gamma = S(1)\times S(2)$, $h$ the identity). The published `agt_regret` defines `AGT.IsCorrelatedEquilibrium ε cost Q` in cost form over a product of players; the paper's CE is its $\varepsilon = 0$ case with cost $-u_i$ and two players, but it is not imported. Best-reply functions are arbitrary stationary selections, which include the paper's lowest-index rule.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 42, Section 2 (the game); p. 43, Section 2, Definition (correlated equilibrium); p. 44, Section 3 (D_t and tie-breaking); p. 45, proof of Theorem 1 (M_b(x))

import Mathlib

namespace CalibratedCE.Generic

/-- A probability vector on a finite set `α`: nonnegative entries summing to one. -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- A joint distribution over `S(1) × S(2) = Fin m × Fin n`. -/
def IsJointDist {m n : ℕ} (D : Fin m → Fin n → ℝ) : Prop :=
  (∀ a b, 0 ≤ D a b) ∧ ∑ a, ∑ b, D a b = 1

/-- Correlated equilibrium of the two-player game `(u₁, u₂)` (players maximize), in the reduced
form of Foster–Vohra p. 44: a joint distribution `D` such that no player gains by composing their
recommendation with a deviation map `Φ`. -/
def IsCE {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (D : Fin m → Fin n → ℝ) : Prop :=
  IsJointDist D ∧
  (∀ Φ : Fin m → Fin m, ∑ a, ∑ b, D a b * u₁ (Φ a) b ≤ ∑ a, ∑ b, D a b * u₁ a b) ∧
  (∀ Φ : Fin n → Fin n, ∑ a, ∑ b, D a b * u₂ a (Φ b) ≤ ∑ a, ∑ b, D a b * u₂ a b)

/-- `π(G)`: the set of correlated equilibria of the game `(u₁, u₂)`. -/
def CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {D | IsCE u₁ u₂ D}

/-- `R₁` is a stationary deterministic best-reply function of player 1: at every forecast `p`
(a probability vector over player 2's strategies) it selects a best response to `p`. -/
def IsBestReply₁ {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (R₁ : (Fin n → ℝ) → Fin m) : Prop :=
  ∀ p, IsDist p → ∀ a', ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ (R₁ p) b

/-- `R₂` is a stationary deterministic best-reply function of player 2. -/
def IsBestReply₂ {m n : ℕ} (u₂ : Fin m → Fin n → ℝ) (R₂ : (Fin m → ℝ) → Fin n) : Prop :=
  ∀ q, IsDist q → ∀ b', ∑ a, q a * u₂ a b' ≤ ∑ a, q a * u₂ a (R₂ q)

/-- `M_b(x)`: the mixtures over player 2's strategies to which `a` is a best response of
player 1. -/
def Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m) : Set (Fin n → ℝ) :=
  {p | IsDist p ∧ ∀ a', ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ a b}

/-- `D_t(x, y)`: the fraction of the first `t` rounds (rounds `0, …, t-1`) in which player 1
plays `a` and player 2 plays `b`. At `t = 0` the value is `0`. -/
noncomputable def empDist {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ)
    (a : Fin m) (b : Fin n) : ℝ :=
  (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) / t

end CalibratedCE.Generic


