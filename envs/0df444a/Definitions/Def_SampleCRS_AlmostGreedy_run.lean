-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_run
-- name    : SampleCRS_AlmostGreedy_run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:25.916743+00:00
-- url     : https://prove2.me/theorems/dccf3705-c59b-48de-ab19-8aeab5439db1
-- title:
--   Algorithm 4: the Almost-Greedy online run
-- statement:
--   For an integer capacity $k\ge1$, fix an arrival permutation $\sigma$, online activations $X$, samples $Y$, and a Boolean coin $Q$. The state consists of an accepted set $\mathcal A$ and a flag, initialized to $\varnothing$ and False. At time $t$, element $\sigma(t)$ arrives. Inactive elements are rejected. An active element is accepted when $|\mathcal A|<k-1$. When $|\mathcal A|=k-1$ and the flag is False, it is accepted if its sample is inactive; otherwise the flag becomes True and it is accepted exactly when $Q=1$. When $|\mathcal A|=k-1$ and the flag is True, the active element is accepted. All remaining cases are rejected.
--
--   $$\operatorname{run}(k,\sigma,X,Y,Q)=\text{the accepted set after folding these transitions over }t=0,\ldots,n-1.$$
--
--   This is the algorithm whose performance is asserted by Theorem 4.1. It receives no activation probabilities. One coin drawn before the run has the same law as the coin drawn at line 12, since that line is reached at most once. The definition remains total at $k=0$, but all claims about the scheme require $k\ge1$.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Algorithm 4, p.14

import Mathlib

namespace SampleCRS.AlmostGreedy

/-- One arrival of Algorithm 4, lines 3–22, p.14. State is (accepted set, flag).
The unique acceptance coin is sampled before the run. -/
def step {n : ℕ} (k : ℕ) (X Y : Fin n → Bool) (Q : Bool)
    (state : Finset (Fin n) × Bool) (i : Fin n) : Finset (Fin n) × Bool :=
  if X i = true then
    if state.1.card < k - 1 then
      (insert i state.1, state.2)
    else if state.1.card = k - 1 ∧ state.2 = false then
      if Y i = false then (insert i state.1, state.2)
      else if Q = true then (insert i state.1, true)
      else (state.1, true)
    else if state.1.card = k - 1 ∧ state.2 = true then
      (insert i state.1, state.2)
    else state
  else state

/-- Algorithm 4 as an online fold. At time t, element σ t arrives.
Neither the step nor the run has access to p. -/
def run {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) (X Y : Fin n → Bool)
    (Q : Bool) : Finset (Fin n) :=
  ((List.finRange n).foldl (fun state t => step k X Y Q state (σ t)) (∅, false)).1

end SampleCRS.AlmostGreedy


