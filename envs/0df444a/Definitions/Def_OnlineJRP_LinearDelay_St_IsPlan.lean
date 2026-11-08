-- Prove2me | Definitions.Def_OnlineJRP_LinearDelay_St_IsPlan
-- name    : OnlineJRP_LinearDelay_St_IsPlan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:53.226312+00:00
-- url     : https://prove2.me/theorems/46222654-663d-406b-8371-a5f1e5fd1f99
-- title:
--   PlanPurchase: the deadline order, the mature items, the returned $(S,s)$ and the refused item
-- statement:
--   Algorithm 3 at a call at time $t$: let $i_1,\dots,i_k$ be the active items in increasing order of $\tau_i$, ties broken by a fixed order on the items. Let $m$ be maximal with
--   $$
--   1+\sum_{j=1}^m u_{i_j}(\tau_{\min})\le \mathrm{sl}(\tau_{\min}).
--   $$
--   Set $S=\{i:u_i(\tau_{\min})=0\}\cup\{i_1,\dots,i_m\}$ and let $s$ be the earliest $s\in[t,\tau_{\min}]$ with $\mathrm{sl}(s)\ge 1+\sum_{i\in S}u_i(s)$. The **refused item** of the purchase (p. 13) is the first item of the deadline order outside $S$.
--
--   **Formalization Note** The set of mature items is read over active items. The predicate says that $(S,s)$ is what the algorithm returns: maximality and earliestness are `IsGreatest` and `IsLeast`, which hold only when such an $m$ and $s$ exist, so the predicate does not assume that the algorithm is well defined. The tie-break is the lexicographic order on $(\tau_i,i)$.
-- source:
--   Baligács, Chang, Coester, Optimal Online Joint Replenishment with Linear Delays (preprint, sha256 116bba5b…), Algorithm 3, p. 9; the refused item, p. 13

import Mathlib
import Definitions.Def_OnlineJRP_LinearDelay_St_sl

namespace OnlineJRP.LinearDelay

namespace St

open Finset

variable {n : ℕ}

/-- The active items sorted in increasing order of `τ_i`, breaking ties by a fixed order on the items
(Algorithm 3, line 1, p. 9, and the sentence before it): sorted by the pair `(τ_i, i)`, lexicographically. -/
noncomputable def deadlineOrder (st : St n) : List (Fin n) :=
  ((st.active.image fun i => toLex (st.τi i, i)).sort (· ≤ ·)).map fun q => (ofLex q).2

open Classical in
/-- The items that are mature at the checkpoint: the set `{i : u_i(τmin) = 0}` of Algorithm 3, line 3
(p. 9).

**Formalization Note** The set is read over active items, as `S` is the set "of all items that reach
maturity" among those with live requests (p. 8). An inactive item with `c_i = 0` has `u_i = 0` by
formula and would otherwise be a spurious member. -/
noncomputable def mature (st : St n) (x : ℝ) (c : Fin n → ℝ) : Finset (Fin n) :=
  st.active.filter fun i => st.u x c i st.τmin = 0

open Classical in
/-- `PlanPurchase` (Algorithm 3, p. 9) can return `(S, s)`: with `i_1, …, i_k` the deadline order, `m`
is maximal such that `1 + ∑_{j ≤ m} u_{i_j}(τmin) ≤ sl(τmin)`, `S` is the set of mature items together
with `i_1, …, i_m`, and `s` is the earliest `s ∈ [t, τmin]` with `sl(s) ≥ 1 + ∑_{i ∈ S} u_i(s)`.

**Formalization Note** `IsGreatest` and `IsLeast` hold only when a maximum `m` and an earliest `s`
exist, never by default. Their existence at every call is what the paper proves (Observation 4,
Proposition 5); this predicate does not assume it. -/
def IsPlan (st : St n) (x : ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)) (s : ℝ) : Prop :=
  ∃ m : ℕ,
    IsGreatest {m | m ≤ st.deadlineOrder.length ∧
      1 + ((st.deadlineOrder.take m).map fun i => st.u x c i st.τmin).sum ≤ st.sl x c st.τmin} m ∧
    S = st.mature x c ∪ (st.deadlineOrder.take m).toFinset ∧
    IsLeast {s | s ∈ Set.Icc st.now st.τmin ∧ 1 + ∑ i ∈ S, st.u x c i s ≤ st.sl x c s} s

open Classical in
/-- The refused item of a purchase of `S` planned at this call (p. 13): the first item of the call's
deadline ordering not in `S`, if any. -/
noncomputable def refused (st : St n) (S : Finset (Fin n)) : Option (Fin n) :=
  st.deadlineOrder.find? fun i => i ∉ S

end St

end OnlineJRP.LinearDelay


