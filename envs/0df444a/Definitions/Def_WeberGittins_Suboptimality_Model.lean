-- Prove2me | Definitions.Def_WeberGittins_Suboptimality_Model
-- name    : WeberGittins_Suboptimality_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:22.223984+00:00
-- url     : https://prove2.me/theorems/f7f63e32-29a8-43f2-a0b9-1346d73deb4d
-- title:
--   Section 1 and (3), pp. 1024–1027 — Weber's index G = γ/(1 − β), bounded nonnegative rewards, round expectations
-- statement:
--   This module adds three objects to the discounted $k$-armed Markov bandit of the published `GittinsIndex` model (one kernel $P$ on a measurable state space $S$, a reward function $r : S \to \mathbb{R}$, a discount factor $\beta$, and history-dependent randomized policies $\pi$).
--
--   1. **Weber's Gittins index.** For a state $y$, with $\gamma(y)$ the fair charge (the published Gittins index, the ratio (4) of the paper),
--   $$G(y) \;=\; \frac{\gamma(y)}{1-\beta}.$$
--   This is Weber's equation (3). The fair charge $\gamma$ and the index $G$ are different numbers; Weber writes $G$ in Theorem 2 and $\gamma$ in (5).
--
--   2. **Standing assumption on rewards.** Weber's Section 1 says "Assume rewards are nonnegative and uniformly bounded." The predicate holds for $r$ when $r(y) \ge 0$ for every state $y$ and there is a constant $C$ with $r(y) \le C$ for every $y$.
--
--   3. **Round-$t$ expectation.** For a policy $\pi$, an initial state vector $x$, a round $t \ge 0$ and a function $f$ of the history of the first $t$ rounds (which records the state vectors $x(0),\dots,x(t-1)$, the arms played in those rounds, and the current state vector $x(t)$) and of the arm $j(t)$ played in round $t$,
--   $$\mathbb{E}_\pi\big[f(\text{history up to } t,\ j(t)) \,\big|\, x(0)=x\big].$$
--   It is computed under the law of the first $t+1$ rounds. With $f = r(x_{j(t)}(t))$ it is the expected reward of round $t$, so the published value $V_\pi(x) = \sum_t \beta^t\, \mathbb{E}_\pi[r(x_{j(t)}(t))]$ is a series of such expectations.
--
--   These objects let the statements of the mission be written in Weber's notation: $G$ for the index, the standing assumption as a hypothesis, and every $E_\pi[\sum_t \beta^t (\cdot)]$ of the paper as a series of round expectations.
--
--   **Formalization Note** Weber's $n$ bandits each have their own state space, kernel and reward; the published model has one $S$, $P$, $r$, which covers that case by taking the disjoint union of the state spaces. The reward $r$ is the conditional mean of Weber's random reward $R_j(x_j(t))$, which is all that enters the expectations. Time is indexed from $0$ as in Weber's (1).
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), pp. 1024 and 1027, Section 1 and eq. (3)

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Suboptimality

/-- Weber (3), p. 1027: the Gittins index G_j(x_j) = γ_j(x_j)/(1 − β), with γ the fair charge
(`gittinsIndex`, the ratio (4)). -/
noncomputable def weberIndex {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (β : ℝ) (y : S) : ℝ :=
  gittinsIndex P r β y / (1 - β)

/-- Weber's standing assumption, Section 1, p. 1024: "Assume rewards are nonnegative and uniformly
bounded." -/
def RewardsNonnegBounded {S : Type*} (r : S → ℝ) : Prop :=
  (∀ y, 0 ≤ r y) ∧ ∃ C : ℝ, ∀ y, r y ≤ C

/-- E_π[f(history of the first t rounds, current states at t; arm j(t) played at t) | x(0) = x]:
the round-t expectation under the horizon-(t+1) law. With `f h j = r (h.2 j)` it is
`markovBanditRoundReward P r π x t`. -/
noncomputable def roundExpectation {S : Type*} [MeasurableSpace S] {k : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π : MarkovBanditPolicy k S) (x : Fin k → S) (t : ℕ)
    (f : MarkovBanditHistory k S t → Fin k → ℝ) : ℝ :=
  ∫ h, f (truncateMarkovBanditHistory h) (h.1 (Fin.last t)).2 ∂markovBanditMeasure P π x (t + 1)

end WeberGittins.Suboptimality


