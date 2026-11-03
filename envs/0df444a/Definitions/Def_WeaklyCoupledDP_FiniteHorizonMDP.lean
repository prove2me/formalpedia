-- Prove2me | Definitions.Def_WeaklyCoupledDP_FiniteHorizonMDP
-- name    : WeaklyCoupledDP_FiniteHorizonMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:11.722391+00:00
-- url     : https://prove2.me/theorems/f3e942cd-4dd3-400a-b4bb-3405686c41d4
-- title:
--   Finite-horizon Markov decision process with time-indexed finite state spaces and its backward-induction value
-- statement:
--   A **finite-horizon Markov decision process** with horizon $T$ consists of, for every period $t$:
--
--   1. a finite state space $X_t$ (the state space $X_{T+1}$ is the terminal one);
--   2. for every state $x \in X_t$, a finite set of available actions $\mathrm{avail}_t(x)$, nonempty for $1 \le t \le T$;
--   3. a one-period reward $\mathrm{reward}_t(x, u) \in \mathbb R$;
--   4. transition probabilities $\mathrm{kernel}_t(x, u, y)$ from $x \in X_t$ to $y \in X_{t+1}$, nonnegative and summing to one over $y$ whenever $1 \le t \le T$ and $u$ is available at $x$.
--
--   Its **optimal value** is computed by backward induction from the terminal value $V_{T+1} \equiv 0$:
--   $$
--   V_t(x) = \max_{u \in \mathrm{avail}_t(x)} \Big\{ \mathrm{reward}_t(x,u) + \sum_{y \in X_{t+1}} \mathrm{kernel}_t(x,u,y)\, V_{t+1}(y) \Big\}, \qquad 1 \le t \le T,
--   $$
--   and $V_t \equiv 0$ for $t > T$. The module also proves the two defining equations (the Bellman equation for $t \le T$ and $V_t = 0$ for $t > T$).
--
--   This is the common shape of the three dynamic programs of Brown and Zhang's paper: the weakly coupled DP (2) on the joint state $(s_t, e_t)$, its Lagrangian relaxation (§3.2), and the single-subproblem DP of Proposition 3.2(b). Each of them is an instance of this structure.
--
--   **Formalization Note** Periods are natural numbers and $1$-based. The maximum of a function over a finite set is written `maxOver`; on an empty set it would return the junk value $0$, which never occurs because the action sets are nonempty in periods $1,\dots,T$. Rewards and transition probabilities at unavailable actions are not part of the model and are not constrained.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), §2, p.4 (PDF p.5), the DP (2); §3.2, p.8 (PDF p.9); Proposition 3.2(b), p.8 (PDF p.9)

import Mathlib

open Finset

namespace WeaklyCoupledDP

/-- The maximum of `f` over a finite set `A`. The value `0` on an empty `A` is a junk value: every
use in this development has a nonempty `A` (`FiniteHorizonMDP.avail_nonempty`). -/
noncomputable def maxOver {α : Type*} (A : Finset α) (f : α → ℝ) : ℝ :=
  if h : A.Nonempty then A.sup' h f else 0

/-- **A finite-horizon Markov decision process** with periods `t ∈ {1, …, T}`, time-indexed finite
state spaces `X t` (the state space `X (T + 1)` is the terminal one), action types `U t`,
state-dependent finite action sets `avail t x`, one-period rewards `reward t x u` and transition
probabilities `kernel t x u y` from `x` in period `t` to `y` in period `t + 1`.

This is the common shape of the three dynamic programs of Brown & Zhang, *On the Strength of
Relaxations of Weakly Coupled Stochastic Dynamic Programs*, SSRN 3849573 (Feb. 6, 2022): the DP (2),
p.4, the Lagrangian DP of §3.2, p.8, and the subproblem DP of Proposition 3.2(b), p.8.

**Formalization Note.** Periods are natural numbers, `1`-based. Every condition is restricted to
`1 ≤ t ≤ T`, and the probability conditions to available actions: `reward` and `kernel` at an action
`u ∉ avail t x` are junk values nothing constrains. -/
structure FiniteHorizonMDP (T : ℕ) (X U : ℕ → Type*) [∀ t, Fintype (X t)] where
  /-- The finite action sets. -/
  avail : ∀ t, X t → Finset (U t)
  /-- The one-period rewards. -/
  reward : ∀ t, X t → U t → ℝ
  /-- The transition probabilities. -/
  kernel : ∀ t, X t → U t → X (t + 1) → ℝ
  avail_nonempty : ∀ t, 1 ≤ t → t ≤ T → ∀ x, (avail t x).Nonempty
  kernel_nonneg : ∀ t, 1 ≤ t → t ≤ T → ∀ x u, u ∈ avail t x → ∀ y, 0 ≤ kernel t x u y
  kernel_sum : ∀ t, 1 ≤ t → t ≤ T → ∀ x u, u ∈ avail t x → ∑ y, kernel t x u y = 1

namespace FiniteHorizonMDP

variable {T : ℕ} {X U : ℕ → Type*} [∀ t, Fintype (X t)] (M : FiniteHorizonMDP T X U)

/-- Backward induction with `k` periods to go, starting in period `t`: `0` at `k = 0`, and
`max_{u ∈ avail t x} { reward t x u + ∑ y, kernel t x u y * (value of y in period t + 1) }`
otherwise. -/
noncomputable def valueToGo : ℕ → ∀ t, X t → ℝ
  | 0, _, _ => 0
  | k + 1, t, x =>
      maxOver (M.avail t x) fun u =>
        M.reward t x u + ∑ y, M.kernel t x u y * valueToGo k (t + 1) y

/-- The optimal value `V_t(x)` of the Bellman recursion with terminal value `V_{T+1} = 0`. -/
noncomputable def value (t : ℕ) (x : X t) : ℝ :=
  M.valueToGo (T + 1 - t) t x

/-- The terminal condition: `V_t = 0` after the last period. -/
theorem value_of_lt {t : ℕ} (ht : T < t) (x : X t) : M.value t x = 0 := by
  have h : T + 1 - t = 0 := by omega
  simp [value, h, valueToGo]

/-- The Bellman equation in every period `t ≤ T`. -/
theorem value_of_le {t : ℕ} (ht : t ≤ T) (x : X t) :
    M.value t x = maxOver (M.avail t x) fun u =>
      M.reward t x u + ∑ y, M.kernel t x u y * M.value (t + 1) y := by
  have h : T + 1 - t = (T + 1 - (t + 1)) + 1 := by omega
  simp only [value]
  rw [h, valueToGo]

end FiniteHorizonMDP

end WeaklyCoupledDP


