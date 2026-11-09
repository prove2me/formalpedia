-- Prove2me | Definitions.Def_CutRankSched_dpSet
-- name    : CutRankSched_dpSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:36:12.209515+00:00
-- url     : https://prove2.me/theorems/6d2ba617-a84d-4ef7-9e01-44a473ca9aad
-- title:
--   State sets $\mathrm{DP}$ of Algorithm 1 at each cut
-- statement:
--   The **state set** of Algorithm 1 at cut $k$ is defined by the algorithm's own recursion (lines 5–17):
--
--   1. at cut $0$, $\mathrm{DP} = \{ ((\{0\})_{s=1}^L, \emptyset) \}$;
--   2. at cut $k+1$, $\mathrm{DP}$ is the set of (canonicalized) successor states of the states at cut $k$ under all legal trial layers for event $k+1$.
--
--   States are compared as subspaces and labellings, which is the canonicalization of line 16.
--
--   **Formalization Note** The recursion is the transition of the algorithm, not the invariant (9); that the two agree is a theorem. Beyond cut $n$ the value is irrelevant and is kept constant.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Algorithm 1, lines 5–17, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_State
import Definitions.Def_CutRankSched_legal
import Definitions.Def_CutRankSched_next

set_option autoImplicit false

namespace CutRankSched

/-- The set `DP` of states held by Algorithm 1 after processing the first `k` events
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Algorithm 1 lines 5–17, p.10): initially the single state `(({0})_{s=1}^L, ∅)`; the
states at cut `k + 1` are the canonicalized successors `next` of the states at cut `k` under the
legal trial layers.

**Formalization Note** "Canonicalized" states are compared as subspaces, so `DP` is a set of
states. The recursion is the algorithm's transition, not the invariant (9). The value at
`k + 1 > n` (no event left) is irrelevant and is set to the value at `k`. -/
noncomputable def dpSet (I : Instance) (L : ℕ) : ℕ → Set (State I L)
  | 0 => {((fun _ => ⊥), (fun _ => none))}
  | k + 1 =>
    if hk : k < I.n then
      {st' | ∃ st ∈ dpSet I L k, ∃ t : Fin L, legal I L ⟨k, hk⟩ st t ∧ st' = next I L ⟨k, hk⟩ st t}
    else dpSet I L k

end CutRankSched


