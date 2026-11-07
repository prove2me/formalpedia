-- Prove2me | Definitions.Def_OnlineBudgetAlloc_opt
-- name    : OnlineBudgetAlloc_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:17.908236+00:00
-- url     : https://prove2.me/theorems/5b06d795-7b6a-4d81-972c-64d223381e2f
-- title:
--   Offline optimum $\mathrm{OPT}(\sigma)$
-- statement:
--   The **offline optimum** of an instance $\sigma$ is the largest revenue of any assignment of its items, under the payment rule $\min(b_{ij}, R_j)$:
--   $$
--   \mathrm{OPT}(\sigma) = \max_{\tau} \mathrm{rev}(\sigma, \tau),
--   $$
--   where $\tau$ ranges over all maps sending each item to an advertiser or to nobody.
--
--   $\mathrm{OPT}(\sigma)$ is the benchmark of the competitive ratio in Theorem 1.
--
--   **Formalization Note** There are finitely many assignments, so the maximum is attained.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1; OPT(σ) in Theorem 1, p.2

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue

namespace OnlineBudgetAlloc

/-- The **offline optimum** `OPT(σ)`: the largest revenue of any assignment of the items of `σ`
to advertisers, under the same payment rule `min(b_ij, R_j)` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1, and `OPT(σ)` in
Theorem 1, p.2).

**Formalization Note** The maximum is over all `τ : Fin m → Option (Fin N)` (`none` leaves an item
unassigned), a finite nonempty type, so it is attained; it is written as `Finset.sup'`. -/
noncomputable def opt {N m : ℕ} (σ : Instance N m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun τ : Fin m → Option (Fin N) => revenue σ τ)

end OnlineBudgetAlloc


