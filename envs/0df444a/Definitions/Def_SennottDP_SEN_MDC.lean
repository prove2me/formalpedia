-- Prove2me | Definitions.Def_SennottDP_SEN_MDC
-- name    : SennottDP_SEN_MDC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:45:28.097747+00:00
-- url     : https://prove2.me/theorems/7ec5ffdc-d574-49f9-af47-c5824d5f1529
-- title:
--   Markov decision chain with countable states, finite action sets and nonnegative costs; general and stationary policies
-- statement:
--   A **Markov decision chain** (MDC) $\Delta$ consists of
--
--   1. a countable state space $S$ (finite or denumerably infinite);
--   2. for each state $i \in S$, a finite nonempty set $A_i$ of actions;
--   3. for each $i$ and $a \in A_i$, a nonnegative finite cost $C(i,a)$;
--   4. for each $i$ and $a \in A_i$, a probability distribution $(P_{ij}(a))_{j \in S}$ of the next state, so that $\sum_{j} P_{ij}(a) = 1$.
--
--   A **general policy** $\theta$ observes, at time $n$, the whole history
--   $$h_n = (i_0, a_0, i_1, a_1, \dots, i_{n-1}, a_{n-1}, i_n)$$
--   and chooses the action at time $n$ according to a probability distribution $\theta(\cdot \mid h_n)$ on $A_{i_n}$. Policies may be history dependent and randomized.
--
--   A **stationary policy** $f$ assigns to each state $i$ an action $f(i) \in A_i$ and uses it whenever the current state is $i$; it is the general policy that chooses $f(i_n)$ with probability one after every history $h_n$.
--
--   These are the objects every average cost result of Chapter 7 is stated for.
--
--   **Formalization Note** Actions live in a type `Act`, and `A i : Finset Act`. Transition probabilities are `ℝ≥0∞`-valued with `∑' j, P i a j = 1` required for `a ∈ A i`. A history at time $n$ is a state sequence `Fin (n+1) → S` and an action sequence `Fin n → Act`; a policy gives, for every such pair, a distribution supported on the action set of the last state.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 16, Section 2.1 (the MDC); pp. 20–22, Section 2.2 (policies); p. 127 (countable state space)

import Mathlib
import Definitions.Def_SennottDP_Discounted_MDC

open scoped ENNReal NNReal

namespace SennottDP.SEN

/-- Sennott (1999), §2.2, p. 20: a stationary policy `f` chooses the action `f(i) ∈ A_i` whenever
the current state is `i`. -/
def StationaryPolicy {S : Type} [Countable S] {Act : Type} (M : SennottDP.Discounted.MDC S Act) : Type :=
  {f : S → Act // ∀ i, f i ∈ M.A i}

open Classical in
/-- A stationary policy `f` viewed as a general policy: at every time `n` and after every history
`h_n`, it chooses the action `f(i_n)` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {S : Type} [Countable S] {Act : Type} {M : SennottDP.Discounted.MDC S Act}
    (f : StationaryPolicy M) : SennottDP.Discounted.Policy M where
  dist n s _ a := if a = f.1 (s (Fin.last n)) then 1 else 0
  dist_supp n s _ a ha := by
    have hne : a ≠ f.1 (s (Fin.last n)) := fun h => ha (h ▸ f.2 _)
    simp [hne]
  dist_sum n s _ := by
    simp [f.2 (s (Fin.last n))]

end SennottDP.SEN


