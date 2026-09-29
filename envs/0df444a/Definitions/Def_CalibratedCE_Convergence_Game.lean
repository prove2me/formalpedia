-- Prove2me | Definitions.Def_CalibratedCE_Convergence_Game
-- name    : CalibratedCE_Convergence_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:26:15.424327+00:00
-- url     : https://prove2.me/theorems/eeeece0f-69f8-4bc2-a210-eb3235ca361d
-- title:
--   Two-player finite game, probability vectors and correlated equilibrium (Section 2–3, pp. 42–44)
-- statement:
--   Foster and Vohra (p. 42) fix a finite two-player game: "For $i = 1, 2$, denote by $S(i)$ the finite set of pure strategies of player $i$ and by $u_i(x, y) \in \mathbb{R}$ the payoff to player $i$ where $x \in S(1)$ and $y \in S(2)$. Let $m = |S(1)|$ and $n = |S(2)|$." Here $S(1) = \{0,\dots,m-1\}$, $S(2) = \{0,\dots,n-1\}$, and the payoffs are two real $m \times n$ matrices $u_1, u_2$, which the players maximize.
--
--   This file defines four objects.
--
--   1. A **probability vector** on a finite set $A$ is $p : A \to \mathbb{R}$ with $p_a \ge 0$ for all $a$ and $\sum_a p_a = 1$.
--   2. A **joint distribution** on $S(1) \times S(2)$ is a matrix $D$ with $D(x, y) \ge 0$ and $\sum_{x, y} D(x, y) = 1$.
--   3. A joint distribution $D$ is a **correlated equilibrium** of $G = (u_1, u_2)$ if no player gains by applying a deviation map to the strategy recommended to them:
--   $$\sum_{x, y} D(x, y)\, u_1(\Phi(x), y) \le \sum_{x, y} D(x, y)\, u_1(x, y) \quad \text{for all } \Phi : S(1) \to S(1),$$
--   $$\sum_{x, y} D(x, y)\, u_2(x, \Phi(y)) \le \sum_{x, y} D(x, y)\, u_2(x, y) \quad \text{for all } \Phi : S(2) \to S(2).$$
--   4. $\pi(G)$ is the set of all correlated equilibria of $G$.
--
--   The paper's definition (p. 43) reads: "A correlated strategy $h$ is called a correlated equilibrium if $E(u_1(h_1, h_2)) \ge E(u_1(\Phi(h_1), h_2))$ for all $\Phi : S(1) \to S(1)$, and $E(u_2(h_1, h_2)) \ge E(u_2(h_1, \Phi(h_2)))$ for all $\Phi : S(2) \to S(2)$", and p. 44 reduces it: "It is clear from the definition of correlated strategies that a CE is simply a joint distribution over $S(1) \times S(2)$ with a particular property." The definition above is that reduced form.
--
--   These objects are the target of Theorem 1: the empirical distribution of play approaches $\pi(G)$.
--
--   **Formalization Note** A correlated strategy $h : \Gamma \to S(1) \times S(2)$ on a finite probability space is represented by its law, i.e. $\Gamma = S(1) \times S(2)$ and $h$ the identity, as the paper does on p. 44. Strategies are `Fin m` and `Fin n`. `IsCE u₁ u₂ D` is the $\varepsilon = 0$ case of `AGT.IsCorrelatedEquilibrium` of the published definition `agt_regret`, taken with two players and cost $= -u_i$; it is restated here in the paper's two-player payoff form rather than imported.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 42, Section 2 (the game); p. 43, Section 2, Definition (correlated equilibrium); p. 44, Section 3 (CE as a joint distribution); p. 44, Theorem 1 (π(G))

import Mathlib

namespace CalibratedCE.Convergence

/-- A probability vector on a finite set `α`: nonnegative entries summing to one. -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- A joint distribution on `Fin m × Fin n`, written as an `m × n` matrix. -/
def IsJointDist {m n : ℕ} (D : Fin m → Fin n → ℝ) : Prop :=
  (∀ a b, 0 ≤ D a b) ∧ ∑ a, ∑ b, D a b = 1

/-- Correlated equilibrium of the two-player game with payoff matrices `u₁ u₂` (both players
maximize), in the joint-distribution form of Foster–Vohra (1997), p. 44: no player gains by
applying a deviation map `Φ` to the strategy recommended to them. -/
def IsCE {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (D : Fin m → Fin n → ℝ) : Prop :=
  IsJointDist D ∧
  (∀ Φ : Fin m → Fin m, ∑ a, ∑ b, D a b * u₁ (Φ a) b ≤ ∑ a, ∑ b, D a b * u₁ a b) ∧
  (∀ Φ : Fin n → Fin n, ∑ a, ∑ b, D a b * u₂ a (Φ b) ≤ ∑ a, ∑ b, D a b * u₂ a b)

/-- `π(G)`: the set of correlated equilibria of the game `G = (u₁, u₂)`. -/
def CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {D | IsCE u₁ u₂ D}

end CalibratedCE.Convergence


