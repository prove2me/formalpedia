-- Prove2me | Definitions.Def_OnlineBudgetAlloc_DetAlg
-- name    : OnlineBudgetAlloc_DetAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:16.003948+00:00
-- url     : https://prove2.me/theorems/2ae4e8d5-c0c6-40ba-942f-45712cd3f82f
-- title:
--   Deterministic online algorithm and its revenue $\mathrm{ALG}_A(\sigma)$
-- statement:
--   A **deterministic online algorithm** $A$ for $N$ advertisers decides, when an item arrives, which advertiser receives it (or that nobody does). It sees the number of items $m$, the budgets $(B_j)_j$, and the bid vectors $(b_{0\,\cdot}), \dots, (b_{i\,\cdot})$ of all items that have arrived, the current item $i$ last. It does not see later items.
--
--   Running $A$ on an instance $\sigma$ gives an assignment $\tau_A$, and its revenue is
--   $$
--   \mathrm{ALG}_A(\sigma) = \mathrm{rev}(\sigma, \tau_A).
--   $$
--
--   **Formalization Note** The algorithm is not told its own earlier decisions, since it can recompute them from the same data. Telling it the item count $m$ only enlarges the class of algorithms: an algorithm that ignores $m$ is a special case. The auxiliary `bidPrefix σ t` is the list of bid vectors of items $0, \dots, t$.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1; §3.2, p.3

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue

namespace OnlineBudgetAlloc

/-- A **deterministic online algorithm** for online budgeted allocation with `N` advertisers
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1, and "any deterministic online algorithm", §3.2, p.3). When an item arrives, the
algorithm chooses an advertiser (or none) from what it has seen: the number of items `m`, the
budgets, and the bids of all items so far, the current item last.

**Formalization Note** `decide m B h` is the decision for the item whose bid vector is the last
entry of the list `h`; `h` holds the bid vectors of items `0, …, i` in arrival order, so the
decision cannot depend on later items. The algorithm need not be told its own earlier choices:
it can recompute them from the same data. Letting it know the item count `m` is more general than
the paper's model (an algorithm that ignores `m` is a special case). `none` leaves the item
unassigned. -/
structure DetAlg (N : ℕ) where
  /-- The decision rule: item count, budgets, bid history (current item last) ↦ advertiser. -/
  decide : ℕ → (Fin N → ℝ) → List (Fin N → ℝ) → Option (Fin N)

/-- The bid vectors of items `0, …, t` of `σ`, in arrival order: what an online algorithm has seen
when item `t` arrives. -/
def bidPrefix {N m : ℕ} (σ : Instance N m) (t : Fin m) : List (Fin N → ℝ) :=
  List.ofFn (fun k : Fin (t.val + 1) => σ.b ⟨k.val, by have := k.isLt; have := t.isLt; omega⟩)

/-- The assignment produced by the online algorithm `A` on the instance `σ`: item `t` goes to
`A.decide m σ.B (bidPrefix σ t)`. -/
def DetAlg.assign {N m : ℕ} (A : DetAlg N) (σ : Instance N m) : Fin m → Option (Fin N) :=
  fun t => A.decide m σ.B (bidPrefix σ t)

/-- `ALG_A(σ)`: the revenue of the deterministic online algorithm `A` on the instance `σ`
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1). -/
noncomputable def DetAlg.alg {N m : ℕ} (A : DetAlg N) (σ : Instance N m) : ℝ :=
  revenue σ (A.assign σ)

end OnlineBudgetAlloc


