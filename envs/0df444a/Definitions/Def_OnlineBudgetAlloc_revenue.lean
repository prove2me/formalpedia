-- Prove2me | Definitions.Def_OnlineBudgetAlloc_revenue
-- name    : OnlineBudgetAlloc_revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:21.293017+00:00
-- url     : https://prove2.me/theorems/700e9804-5bee-4d34-a573-b9b36c80db67
-- title:
--   Sequential payment rule $\min(b_{ij}, R_j)$ and the revenue of an assignment
-- statement:
--   Let $\tau$ assign each item $i$ either to an advertiser $\tau(i)$ or to nobody. Items are processed in arrival order. Each advertiser $j$ starts with remaining budget $R_j = B_j$. When item $i$ is assigned to $j$, it earns the **payment**
--   $$
--   p_i = \min(b_{ij}, R_j),
--   $$
--   and $R_j$ is reduced by $p_i$. An unassigned item earns $0$. The **revenue** of $\tau$ is the sum of all payments,
--   $$
--   \mathrm{rev}(\sigma, \tau) = \sum_{i} p_i .
--   $$
--   For nonnegative budgets and bids this equals $\sum_j \min\bigl(B_j, \sum_{i : \tau(i) = j} b_{ij}\bigr)$.
--
--   This is the paper's payment rule. It is used both for the online algorithm's revenue and for the offline optimum. Any assignment is allowed, including one to an advertiser with no budget left; such an assignment earns the capped amount.
--
--   **Formalization Note** The module also defines the remaining budget $R_j$ just before item $t$ (`remaining`, indexed by the number $t$ of processed items) and the payment of item $t$ (`payment`).
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance

namespace OnlineBudgetAlloc

/-- The remaining budget `R_j` of advertiser `j` just before item `t` arrives, when the items are
assigned by `τ` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1: "earn a payment of min(bij, Rj), where Rj is the remaining budget
of advertiser j. Correspondingly, the remaining budget of advertiser j is reduced by this payment").

**Formalization Note** `τ i = some j` assigns item `i` to advertiser `j`, and `τ i = none` leaves
it unassigned. The index `t : ℕ` counts processed items: `remaining σ τ 0 j = B j`, and processing
item `t` lowers the budget of its recipient by the payment `min (b t j) (R_j)`. Indices `t ≥ m`
change nothing. -/
noncomputable def remaining {N m : ℕ} (σ : Instance N m) (τ : Fin m → Option (Fin N)) :
    ℕ → Fin N → ℝ
  | 0, j => σ.B j
  | t + 1, j =>
    if h : t < m then
      (if τ ⟨t, h⟩ = some j then
        remaining σ τ t j - min (σ.b ⟨t, h⟩ j) (remaining σ τ t j)
      else remaining σ τ t j)
    else remaining σ τ t j

/-- The payment collected for item `t` under the assignment `τ`: `min(b_tj, R_j)` if item `t`
goes to advertiser `j`, where `R_j` is `j`'s remaining budget just before item `t`, and `0` if
the item is left unassigned (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1). -/
noncomputable def payment {N m : ℕ} (σ : Instance N m) (τ : Fin m → Option (Fin N))
    (t : Fin m) : ℝ :=
  match τ t with
  | none => 0
  | some j => min (σ.b t j) (remaining σ τ t.val j)

/-- The **revenue** of the assignment `τ` on the instance `σ`: the sum of the payments
`min(b_ij, R_j)` over all items, processed in arrival order (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1: "the total revenue,
which is the sum of payments for all items").

**Formalization Note** The payment rule is applied sequentially, exactly as on p.1. For
nonnegative budgets and bids this equals the closed form `∑_j min(B_j, ∑_{i : τ i = j} b_ij)`;
any assignment is allowed, including one to an advertiser with no budget left, which earns the
capped amount. -/
noncomputable def revenue {N m : ℕ} (σ : Instance N m) (τ : Fin m → Option (Fin N)) : ℝ :=
  ∑ t, payment σ τ t

end OnlineBudgetAlloc


