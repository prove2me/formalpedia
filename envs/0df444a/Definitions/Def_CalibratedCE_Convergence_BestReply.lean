-- Prove2me | Definitions.Def_CalibratedCE_Convergence_BestReply
-- name    : CalibratedCE_Convergence_BestReply
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:27:25.641262+00:00
-- url     : https://prove2.me/theorems/89284c12-6888-419c-98c2-f70015f2b820
-- title:
--   Stationary best-reply functions and the regions $M_b(x)$, $M_p(x)$ (pp. 44–45)
-- statement:
--   Let $G = (u_1, u_2)$ be a two-player game with $S(1) = \{0,\dots,m-1\}$ and $S(2) = \{0,\dots,n-1\}$. A mixture over $S(2)$ is a probability vector $p \in \mathbb{R}^n$.
--
--   1. A function $R_1$ from vectors in $\mathbb{R}^n$ to $S(1)$ is a **best-reply function** of player 1 if for every probability vector $p$ over $S(2)$ and every $x' \in S(1)$,
--   $$\sum_{y} p_y\, u_1(x', y) \le \sum_y p_y\, u_1(R_1(p), y).$$
--   Symmetrically, $R_2 : \mathbb{R}^m \to S(2)$ is a best-reply function of player 2 if $\sum_x q_x u_2(x, y') \le \sum_x q_x u_2(x, R_2(q))$ for every probability vector $q$ over $S(1)$ and every $y'$.
--   2. For $x \in S(1)$, $M_b(x)$ is the set of mixtures over $S(2)$ to which $x$ is a best response of player 1: the probability vectors $p$ with $\sum_y p_y u_1(x', y) \le \sum_y p_y u_1(x, y)$ for all $x'$.
--   3. For a best-reply function $R_1$ and $x \in S(1)$, $M_p(x)$ is the set of mixtures $p$ over $S(2)$ with $R_1(p) = x$.
--
--   The paper's standing assumption (p. 44): "We assume that when players select their best response (for a given forecast) they use a stationary and deterministic tie breaking rule; say the lowest indexed strategy." A best-reply function is exactly such a rule: it depends on the forecast alone and is the same in every round. The paper's definitions (p. 45): "For each $x \in S(1)$ let $M_b(x)$ be the set of mixtures over $S(2)$ for which $x$ is a best response. [...] Let $M_p(x)$ be the set of mixtures where player 1 actually plays $x$ given that the forecast is in $M_p(x)$."
--
--   These are the objects of the proof of Theorem 1, which shows that the conditional empirical distribution of player 2's play, given that player 1 plays $x$, ends up in $M_b(x)$.
--
--   **Formalization Note** Theorems quantify over every best-reply function rather than fixing the lowest-index rule; this includes the lowest-index rule, so every statement is at least as strong as the paper's. The value of $R_1$ on vectors outside the simplex is unconstrained; all forecasts are required to be probability vectors.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 44, Section 3 (stationary deterministic tie-breaking); p. 45, proof of Theorem 1 (M_b(x), M_p(x))

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game

namespace CalibratedCE.Convergence

/-- `R₁` is a (stationary, deterministic) best-reply function of player 1: for every
probability vector `p` over player 2's strategies, `R₁ p` maximizes player 1's expected
payoff against `p`. -/
def IsBestReply₁ {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (R₁ : (Fin n → ℝ) → Fin m) : Prop :=
  ∀ p : Fin n → ℝ, IsDist p → ∀ a' : Fin m, ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ (R₁ p) b

/-- `R₂` is a (stationary, deterministic) best-reply function of player 2. -/
def IsBestReply₂ {m n : ℕ} (u₂ : Fin m → Fin n → ℝ) (R₂ : (Fin m → ℝ) → Fin n) : Prop :=
  ∀ q : Fin m → ℝ, IsDist q → ∀ b' : Fin n, ∑ a, q a * u₂ a b' ≤ ∑ a, q a * u₂ a (R₂ q)

/-- `M_b(x)`: the mixtures over player 2's strategies to which `x = a` is a best response of
player 1. -/
def Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m) : Set (Fin n → ℝ) :=
  {p | IsDist p ∧ ∀ a' : Fin m, ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ a b}

/-- `M_p(x)`: the mixtures over player 2's strategies at which player 1, using `R₁`, actually
plays `x = a`. -/
def Mp {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (a : Fin m) : Set (Fin n → ℝ) :=
  {p | IsDist p ∧ R₁ p = a}

end CalibratedCE.Convergence


