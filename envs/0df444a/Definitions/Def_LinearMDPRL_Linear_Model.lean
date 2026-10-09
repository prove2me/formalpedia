-- Prove2me | Definitions.Def_LinearMDPRL_Linear_Model
-- name    : LinearMDPRL_Linear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:58.046899+00:00
-- url     : https://prove2.me/theorems/5c862ff9-8d36-4d01-b645-ff476c93af85
-- title:
--   §2, p. 4 — episodic MDP(S, A, H, P, r) on a measurable state space, policies, V^π and Q^π by (1), V⋆ and Q⋆ by (2)
-- statement:
--   This file sets up the finite-horizon **episodic Markov decision process** $\mathrm{MDP}(\mathcal S,\mathcal A,H,\mathbb P,r)$ of Jin, Yang, Wang and Jordan (§2, p. 4).
--
--   The state space $\mathcal S$ is an arbitrary measurable space (possibly infinite) and the action space $\mathcal A$ is a finite nonempty set. Steps are numbered $h = 1, \dots, H$. For each step $h$:
--
--   1. $\mathbb P_h(\cdot\mid x,a)$ is a Markov kernel from $\mathcal S\times\mathcal A$ to $\mathcal S$: the law of the next state when action $a$ is taken in state $x$;
--   2. $r_h:\mathcal S\times\mathcal A\to[0,1]$ is a deterministic reward, measurable in the state.
--
--   A **policy** $\pi:\mathcal S\times[H]\to\mathcal A$ is deterministic and nonstationary; it is *measurable* if every set $\{x : \pi(x,h)=a\}$ is measurable. Writing $[\mathbb P_h V](x,a) = \int V(x')\,\mathbb P_h(dx'\mid x,a)$, the value and action-value functions of $\pi$ are given by the Bellman equation (1),
--   $$
--   Q^\pi_h(x,a) = (r_h + \mathbb P_h V^\pi_{h+1})(x,a),\qquad V^\pi_h(x) = Q^\pi_h(x,\pi(x,h)),\qquad V^\pi_{H+1} = 0,
--   $$
--   and the optimal value functions by the Bellman optimality equation (2),
--   $$
--   Q^\star_h(x,a) = (r_h + \mathbb P_h V^\star_{h+1})(x,a),\qquad V^\star_h(x) = \max_{a\in\mathcal A} Q^\star_h(x,a),\qquad V^\star_{H+1} = 0.
--   $$
--
--   These objects are what the regret of a learning algorithm is measured against.
--
--   **Formalization Note.** Indices are 1-based as in the paper; $V^\pi_h$ and $V^\star_h$ are computed by backward recursion on the number of remaining steps and are set to $0$ outside $1\le h\le H$ (so $V_{H+1}=0$). The paper *defines* $V^\pi_h$ as an expected sum of rewards and $V^\star_h = \sup_\pi V^\pi_h$, and then states (1) and (2) as consequences; here the recursions (1) and (2) are taken as the definitions, which is the standard equivalent formulation for measurable policies and avoids a supremum over all policies.
-- source:
--   Jin, Yang, Wang, Jordan, Provably Efficient Reinforcement Learning with Linear Function Approximation, arXiv:1907.05388v2, §2, p. 4, equations (1), (2)

import Mathlib

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory

/-- An episodic Markov decision process `MDP(S, A, H, P, r)` (Jin–Yang–Wang–Jordan, §2, p. 4) on a
measurable state space `S` with action space `A`. Steps are indexed by natural numbers used
1-based (`h = 1` is the first step); the horizon `H` is a separate argument of every object built
on the MDP, and the fields at indices outside `1, …, H` are never used.

* `P h` is the transition kernel `P_h(· | x, a)` of step `h`, a Markov kernel from `S × A` to `S`;
* `r h x a` is the deterministic reward `r_h(x, a) ∈ [0, 1]` of step `h`, measurable in `x`. -/
structure EpisodicMDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- The transition kernel `P_h(· | x, a)` of step `h`. -/
  P : ℕ → Kernel (S × A) S
  /-- Every `P_h(· | x, a)` is a probability measure. -/
  isMarkov : ∀ h, IsMarkovKernel (P h)
  /-- The deterministic reward function `r_h` of step `h`. -/
  r : ℕ → S → A → ℝ
  /-- Rewards lie in `[0, 1]`. -/
  r_mem : ∀ h x a, r h x a ∈ Set.Icc (0 : ℝ) 1
  /-- Each reward function is measurable in the state. -/
  r_meas : ∀ h a, Measurable (fun x => r h x a)

/-- A deterministic nonstationary policy `π : S × [H] → A`; `π x h` is the action taken at state
`x` at step `h` (p. 4). -/
abbrev Policy (S A : Type*) := S → ℕ → A

/-- A policy is measurable if, at every step, the set of states where it takes a given action is
measurable. -/
def IsMeasurablePolicy {S A : Type*} [MeasurableSpace S] (π : Policy S A) : Prop :=
  ∀ (h : ℕ) (a : A), MeasurableSet {x | π x h = a}

section Values

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- `valueRem M H π n` is the value of policy `π` with `n` steps remaining, i.e. `V^π_{H+1-n}`,
computed by the Bellman equation (1) (p. 4) backwards from `V^π_{H+1} = 0`. -/
noncomputable def valueRem (M : EpisodicMDP S A) (H : ℕ) (π : Policy S A) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      M.r (H - n) x (π x (H - n)) + ∫ y, valueRem M H π n y ∂(M.P (H - n) (x, π x (H - n)))

/-- The value function `V^π_h(x)` of policy `π` at step `h ∈ [H]`, with `V^π_{H+1} = 0`
(Bellman equation (1), p. 4). It is `0` outside `1 ≤ h ≤ H`. -/
noncomputable def V (M : EpisodicMDP S A) (H : ℕ) (π : Policy S A) (h : ℕ) (x : S) : ℝ :=
  if 1 ≤ h ∧ h ≤ H then valueRem M H π (H + 1 - h) x else 0

/-- The action-value function `Q^π_h(x, a) = (r_h + P_h V^π_{h+1})(x, a)` (Bellman equation (1),
p. 4). -/
noncomputable def Q (M : EpisodicMDP S A) (H : ℕ) (π : Policy S A) (h : ℕ) (x : S) (a : A) : ℝ :=
  M.r h x a + ∫ y, V M H π (h + 1) y ∂(M.P h (x, a))

variable [Fintype A] [Nonempty A]

/-- `optRem M H n` is the optimal value with `n` steps remaining, i.e. `V⋆_{H+1-n}`, computed by
the Bellman optimality equation (2) (p. 4) backwards from `V⋆_{H+1} = 0`. -/
noncomputable def optRem (M : EpisodicMDP S A) (H : ℕ) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      Finset.univ.sup' Finset.univ_nonempty
        (fun a => M.r (H - n) x a + ∫ y, optRem M H n y ∂(M.P (H - n) (x, a)))

/-- The optimal value function `V⋆_h(x) = max_a Q⋆_h(x, a)`, with `V⋆_{H+1} = 0` (Bellman
optimality equation (2), p. 4). It is `0` outside `1 ≤ h ≤ H`. -/
noncomputable def Vstar (M : EpisodicMDP S A) (H : ℕ) (h : ℕ) (x : S) : ℝ :=
  if 1 ≤ h ∧ h ≤ H then optRem M H (H + 1 - h) x else 0

/-- The optimal action-value function `Q⋆_h(x, a) = (r_h + P_h V⋆_{h+1})(x, a)` (equation (2),
p. 4). -/
noncomputable def Qstar (M : EpisodicMDP S A) (H : ℕ) (h : ℕ) (x : S) (a : A) : ℝ :=
  M.r h x a + ∫ y, Vstar M H (h + 1) y ∂(M.P h (x, a))

end Values

end LinearMDPRL.Linear


