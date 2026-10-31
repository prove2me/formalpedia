-- Prove2me | Definitions.Def_RepairSched_Model_allocSet
-- name    : RepairSched_Model_allocSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:09.948334+00:00
-- url     : https://prove2.me/theorems/533464de-3a91-4970-a758-6df570b8f428
-- title:
--   Feasible workload allocations $\mathcal A(w)$
-- statement:
--   For a workload level $w$, the set of feasible allocations of the workload to the queues is
--   $$\mathcal A(w)=\Big\{q\in\mathbb R^n_+ : \sum_i \frac{q_i}{\mu_i}=w\Big\}.$$
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), p.17

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **Feasible workload allocations.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), p.17: `A(w) := {q ∈ ℝ^I₊ : Σᵢ qᵢ/μᵢ = w}`. -/
def Model.allocSet {n : ℕ} (M : Model n) (w : ℝ) : Set (Fin n → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i / M.mu i = w}

end RepairSched


