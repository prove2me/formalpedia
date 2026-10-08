-- Prove2me | Definitions.Def_SennottDP_BOR_MDC
-- name    : SennottDP_BOR_MDC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T10:38:51.489462+00:00
-- url     : https://prove2.me/theorems/31548e0a-dd37-4a47-8536-0d36983ea619
-- title:
--   Markov decision chain with general, stationary and randomized stationary policies
-- statement:
--   A **Markov decision chain** (MDC) $\Delta$ consists of a countable state space $S$; for each state $i$ a finite nonempty set $A_i$ of actions; a nonnegative finite cost $C(i,a)$ incurred when action $a\in A_i$ is chosen in state $i$; and for each $i\in S$, $a\in A_i$ a probability distribution $(P_{ij}(a))_{j\in S}$ of the next state, $\sum_j P_{ij}(a)=1$.
--
--   A **policy** $\theta$ is history dependent and randomized: at time $n$, after the history $h_n=(i_0,a_0,i_1,\dots,a_{n-1},i_n)$, it chooses an action of $A_{i_n}$ according to a probability distribution $\theta(\cdot\mid h_n)$. A **stationary policy** $f$ always chooses $f(i)\in A_i$ in state $i$; a **randomized stationary policy** $d$ chooses $a\in A_i$ with probability $d(a\mid i)$ whenever the state is $i$. Both are regarded as general policies.
--
--   These are the objects on which every statement of this mission is made.
--
--   **Formalization Note** A history at time $n$ is a pair (states `Fin (n+1) → S`, actions `Fin n → Act`). A stationary policy is embedded as the randomized stationary policy with point masses $d(a\mid i)=\mathbf 1\{a=f(i)\}$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 16, 20–22, Sections 2.1–2.2

import Mathlib
import Definitions.Def_SennottDP_Discounted_MDC

open scoped ENNReal NNReal

namespace SennottDP.BOR

/-- Sennott (1999), §2.2, p. 20: a (deterministic) stationary policy `f` chooses the action
`f(i) ∈ A_i` whenever the current state is `i`. -/
def StationaryPolicy {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) : Type :=
  {f : S → Act // ∀ i, f i ∈ M.A i}

/-- Sennott (1999), §2.2, p. 21: a randomized stationary policy `d` chooses, whenever the current
state is `i`, the action `a ∈ A_i` with probability `d(a | i)`, independently of the past. -/
structure RandStationaryPolicy {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) where
  /-- `dist i a = d(a | i)` -/
  dist : S → Act → ℝ≥0∞
  /-- no mass outside `A_i` -/
  dist_supp : ∀ i a, a ∉ M.A i → dist i a = 0
  /-- `d(· | i)` is a probability distribution on `A_i` -/
  dist_sum : ∀ i, ∑ a ∈ M.A i, dist i a = 1

/-- A randomized stationary policy viewed as a general policy: after every history `h_n` it uses
the distribution `d(· | i_n)` of the current state. -/
def RandStationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (d : RandStationaryPolicy M) : SennottDP.Discounted.Policy M where
  dist n s _ a := d.dist (s (Fin.last n)) a
  dist_supp _ _ _ a ha := d.dist_supp _ a ha
  dist_sum _ _ _ := d.dist_sum _

open Classical in
/-- A stationary policy `f` viewed as a randomized stationary policy: `d(a | i) = 1` if
`a = f(i)` and `0` otherwise. -/
noncomputable def StationaryPolicy.toRand {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (f : StationaryPolicy M) : RandStationaryPolicy M where
  dist i a := if a = f.1 i then 1 else 0
  dist_supp i a ha := by
    have hne : a ≠ f.1 i := fun h => ha (h ▸ f.2 i)
    simp [hne]
  dist_sum i := by
    simp [f.2 i]

/-- A stationary policy `f` viewed as a general policy (through its randomized version). -/
noncomputable def StationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type}
    {M : SennottDP.Discounted.MDC S Act} (f : StationaryPolicy M) : SennottDP.Discounted.Policy M :=
  f.toRand.toPolicy

end SennottDP.BOR


