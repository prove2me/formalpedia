-- Prove2me | Definitions.Def_MinimaxRegretRL_Hoeffding_MDP
-- name    : MinimaxRegretRL_Hoeffding_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:25:59.436818+00:00
-- url     : https://prove2.me/theorems/ee149b8d-5213-4607-8f8d-05c7ad68a757
-- title:
--   §2 and Assumption 1 — stationary finite MDP, policies and values
-- statement:
--   A finite-horizon Markov decision process has finite nonempty state and action sets, a stationary transition probability $P(y\mid x,a)$, and a known deterministic reward $R(x,a)\in[0,1]$. A policy chooses an action from the current state and the step within an $H$-step episode. Its value is the expected sum of rewards through the final step, with zero value after step $H$.
--
--   $$V_h^\pi(x)=R(x,\pi(x,h))+\sum_yP(y\mid x,\pi(x,h))V_{h+1}^\pi(y),\qquad V_{H+1}^\pi=0,\qquad V_h^*(x)=\max_\pi V_h^\pi(x).$$
--
--   This definition fixes the model and optimal-value function used throughout the regret theorem. The maximum is over the finite set of deterministic, nonstationary policies.
--
--   **Formalization Note** Lean indexes steps from zero: the Lean argument $h$ is the paper's step $h+1$, so the paper's $V_1$ is the Lean value at $0$ and the paper's $V_{H+1}\equiv0$ is the Lean value at $H$ (and at every later index). The paper's $\sup_\pi$ is taken over the finite type of policies $\mathcal S\times\{0,\dots,H-1\}\to\mathcal A$, where it is a maximum. The transition-row normalization uses the published `IsTransitionKernel` predicate.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), pp. 2–3, §2 and Assumption 1

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace MinimaxRegretRL.Hoeffding

/-- The stationary finite MDP of Azar–Osband–Munos, §2 and Assumption 1. The
general transition-probability condition is reused from the published
`IsTransitionKernel` definition. -/
structure MDP (S A : Type*) [Fintype S] where
  P : S → A → S → ℝ
  kernel : FoundationsML.ReinforcementLearning.IsTransitionKernel P
  R : S → A → ℝ
  reward_mem : ∀ x a, R x a ∈ Set.Icc (0 : ℝ) 1

/-- A deterministic, nonstationary policy for an `H`-step episode. Step zero
in Lean is step one in the paper. -/
abbrev Policy (S A : Type*) (H : ℕ) := S → Fin H → A

/-- Expected reward for the remaining steps, with explicit recursion fuel.
The endpoint `h = H` is zero. -/
noncomputable def policyValueFuel {S A : Type*} [Fintype S]
    (M : MDP S A) (H : ℕ) (π : Policy S A H) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | fuel + 1, h, x =>
      if hh : h < H then
        M.R x (π x ⟨h, hh⟩) +
          ∑ y : S, M.P x (π x ⟨h, hh⟩) y *
            policyValueFuel M H π fuel (h + 1) y
      else 0

/-- The value `Vᵖⁱ_h(x)` of the paper, with paper step `h` represented by
the zero-based natural number `h-1`. -/
noncomputable def policyValue {S A : Type*} [Fintype S]
    (M : MDP S A) (H : ℕ) (π : Policy S A H) (h : ℕ) (x : S) : ℝ :=
  policyValueFuel M H π (H - h) h x

/-- `V*` is the supremum over the finite nonempty type of policies, as
defined on p. 3. -/
noncomputable def optimalValue {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] [Nonempty S] (M : MDP S A) (H h : ℕ) (x : S) : ℝ :=
  by
    classical
    exact Finset.univ.sup' Finset.univ_nonempty
      (fun π : Policy S A H => policyValue M H π h x)

end MinimaxRegretRL.Hoeffding


