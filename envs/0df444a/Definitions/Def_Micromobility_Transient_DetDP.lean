-- Prove2me | Definitions.Def_Micromobility_Transient_DetDP
-- name    : Micromobility_Transient_DetDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:04.307292+00:00
-- url     : https://prove2.me/theorems/9dc77d5d-f959-412d-801d-91f2e993610e
-- title:
--   A discounted deterministic dynamic program: trajectory, discounted cost and value over admissible action sequences
-- statement:
--   This file defines a general discounted deterministic dynamic program.
--
--   A **deterministic dynamic program** consists of a state set $X$, an action set $A$, a predicate singling out the **admissible** actions $\mathcal A \subseteq A$, a transition $f : X \times A \to X$, a per-stage cost $g : X \times A \to \mathbb R$ and a discount factor $\gamma$. For an initial state $x \in X$ and an action sequence $a = (a_0, a_1, \dots)$ the **trajectory** is $x_0 = x$, $x_{k+1} = f(x_k, a_k)$, and the **discounted cost** is
--
--   $$J(x, a) = \sum_{k=0}^{\infty} \gamma^k\, g(x_k, a_k).$$
--
--   The **value** of the program at $x$ is the infimum of the discounted cost over the action sequences all of whose actions are admissible:
--
--   $$V(x) = \inf\big\{J(x, a) \;:\; a_k \in \mathcal A \text{ for every } k\big\}.$$
--
--   In the micromobility model the states are the compact states $\breve x$, the admissible actions are $\hat A$, the transition is (F.1)–(F.5), the stage cost is $\hat c_2(\breve x, \hat a) + \hat N(\hat a)$, and $V$ is the value function $\hat V$.
--
--   **Formalization Note.** $J$ is a `tsum`, which Lean sets to $0$ for a non-summable series, and $V$ is a real infimum over the subtype of admissible sequences, which Lean sets to $0$ if that subtype is empty or $J$ is unbounded below on it. Every use supplies conditions under which the series converges and the infimum is a genuine infimum (in this mission: $0 \le \gamma < 1$ and stage costs bounded on the admissible actions and reachable states). No transition-dependence restriction is built in: the micromobility model's transition ignores the current state, which is a special case.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. 18 (V̂ as a minimum over action sequences) and Proposition F.3, written for a general deterministic program

import Mathlib

namespace Micromobility.Transient

/-! # A discounted deterministic dynamic program

States `X`, actions `A`, an admissible action set, a transition `step`, a per-stage cost and a
discount factor `γ`. A policy is an action sequence `a : ℕ → A`; its cost from `x` is the
discounted sum of the stage costs along the trajectory, and the value is the infimum of that cost
over the admissible sequences. -/

/-- A deterministic dynamic program with discounted cost. -/
structure DetDP (X A : Type*) where
  /-- the admissible actions -/
  admissible : A → Prop
  /-- the next state after taking action `a` at state `x` -/
  step : X → A → X
  /-- the cost incurred by taking action `a` at state `x` -/
  cost : X → A → ℝ
  /-- the discount factor -/
  γ : ℝ

namespace DetDP

variable {X A : Type*} (P : DetDP X A)

/-- The trajectory of an action sequence: `x_0 = x`, `x_{k+1} = step x_k a_k`. -/
def traj (x : X) (a : ℕ → A) : ℕ → X
  | 0 => x
  | k + 1 => P.step (traj x a k) (a k)

/-- The discounted cost `Σ_k γ^k cost(x_k, a_k)` of an action sequence from `x` (a `tsum`). -/
noncomputable def J (x : X) (a : ℕ → A) : ℝ :=
  ∑' k : ℕ, P.γ ^ k * P.cost (P.traj x a k) (a k)

/-- The value `V(x)`: the infimum of `J x a` over the sequences `a` all of whose actions are
admissible (a real `⨅` over that subtype). -/
noncomputable def V (x : X) : ℝ :=
  ⨅ a : {a : ℕ → A // ∀ k, P.admissible (a k)}, P.J x a.1

end DetDP

end Micromobility.Transient


