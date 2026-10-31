-- Prove2me | Definitions.Def_FiniteMemPOMDP_POMDP
-- name    : FiniteMemPOMDP_POMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:11.999191+00:00
-- url     : https://prove2.me/theorems/ce92b85e-29da-427a-bda9-b86e738fcbf6
-- title:
--   Finite POMDP $\Gamma=(\mathcal K,\mathcal A,\mathcal S,q,g)$
-- statement:
--   A **partially observable Markov decision process** (POMDP) $\Gamma=(\mathcal K,\mathcal A,\mathcal S,q,g)$ consists of a finite state space $\mathcal K$, a finite action set $\mathcal A$, a finite signal set $\mathcal S$, a transition function $q:\mathcal K\times\mathcal A\to\Delta(\mathcal K\times\mathcal S)$ and a reward function $g:\mathcal K\times\mathcal A\to[0,1]$.
--
--   When action $a$ is played in state $k$, the decision-maker receives the (unobserved) reward $g(k,a)$, and the pair (next state, signal) is drawn from $q(k,a)$; the decision-maker observes only the signal.
--
--   This is the model of the whole mission: every statement quantifies over all such $\Gamma$.
--
--   **Formalization Note** The sets are the type parameters `K`, `A`, `S`; finiteness and nonemptiness are imposed where the model is used. $q(k,a)$ is a `PMF (K × S)`, a joint law of next state and signal, as printed: it is not split into a transition matrix and an observation matrix, and no entry is required to be positive.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib

namespace FiniteMemPOMDP

/-- **A finite POMDP `Γ = (K, A, S, q, g)`.**
Chatterjee, Saona & Ziliotto, *Finite-memory strategies in POMDPs with Long-run Average
Objectives*, arXiv:1904.13360v2, §2.1, p.2: "Consider a POMDP Γ = (K, A, S, q, g), with finite
state space K, finite action set A, finite signal set S, transition function q: K × A → ∆(K × S)
and reward function g: K × A → [0, 1]."

The state, action and signal sets are the type parameters `K`, `A`, `S` (finiteness and
nonemptiness are imposed where the POMDP is used). `q k a` is the joint law of the pair
(next state, signal) when action `a` is played in state `k`; `g k a ∈ [0, 1]` is the stage
reward.

**Formalization Note** `q` is a joint kernel `K × A → ∆(K × S)`, as printed: it is not split into
a transition and an observation matrix and no entry is required to be positive. `∆(K × S)` is
encoded by `PMF (K × S)`. -/
structure POMDP (K A S : Type) where
  /-- transition function `q : K × A → ∆(K × S)` -/
  q : K → A → PMF (K × S)
  /-- reward function `g : K × A → [0, 1]` -/
  g : K → A → ℝ
  /-- rewards are nonnegative -/
  g_nonneg : ∀ k a, 0 ≤ g k a
  /-- rewards are at most one -/
  g_le_one : ∀ k a, g k a ≤ 1

end FiniteMemPOMDP


