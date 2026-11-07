-- Prove2me | Definitions.Def_FairTeamContracts_IsSuccessFn
-- name    : FairTeamContracts_IsSuccessFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:09.747164+00:00
-- url     : https://prove2.me/theorems/6249ae6e-504f-446b-bc26-752416679335
-- title:
--   Success probability function $f:2^N\to[0,1]$, monotone and normalized
-- statement:
--   A principal hires agents from the set $N=[n]=\{1,\dots,n\}$ for a joint project. The **success probability function** $f:2^N\to[0,1]$ assigns to each set $S\subseteq N$ of agents exerting effort the probability $f(S)$ that the project succeeds. It is assumed
--
--   1. **monotone**: $f(S')\le f(S)$ whenever $S'\subseteq S\subseteq N$;
--   2. **normalized**: $f(\emptyset)=0$;
--   3. valued in $[0,1]$: $0\le f(S)\le1$ for every $S$.
--
--   Since the principal's reward upon success is normalized to $1$, $f(S)$ is also the principal's expected reward, and $f$ is called the reward function. Every result of the mission is stated for such $f$.
--
--   **Formalization Note** Agents are `Fin n` (indexed from $0$) and sets of agents are `Finset (Fin n)`. Monotonicity is the published `SubsamplingSM.Offline.IsMonotoneSetFn`.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2 Model, p.7

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace FairTeamContracts

/-- **Success probability function** of the team-production model (Chen, Castiglioni, Li,
*Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2 Model, p.7):
`f : 2^N → [0, 1]`, monotone (`f(S′) ≤ f(S)` for `S′ ⊆ S ⊆ N`) and normalized (`f(∅) = 0`).
Because the success reward is normalized to 1 (p.8), `f(S)` is also the principal's expected
reward when the agents in `S` exert effort, so the paper also calls `f` the reward function.

**Formalization Note.** The agent set `N = [n]` is `Fin n` (agents are indexed from `0`), and
sets of agents are `Finset (Fin n)`. Monotonicity is the published
`SubsamplingSM.Offline.IsMonotoneSetFn`. The codomain `[0, 1]` is the clause `0 ≤ f S ≤ 1` for
every `S`. -/
def IsSuccessFn {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  SubsamplingSM.Offline.IsMonotoneSetFn f ∧ f ∅ = 0 ∧ ∀ S, 0 ≤ f S ∧ f S ≤ 1

end FairTeamContracts


