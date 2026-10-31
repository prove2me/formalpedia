-- Prove2me | Definitions.Def_RepairSched_Model_invWork
-- name    : RepairSched_Model_invWork
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:51.00438+00:00
-- url     : https://prove2.me/theorems/d01d7203-a768-49f7-9d43-9050f0d8718d
-- title:
--   Workload held in inventory $\sum_i S_i/\mu_i$
-- statement:
--   For an inventory vector $S$, the workload held in inventory is
--   $$\sum_{i} \frac{S_i}{\mu_i}.$$
--   It is the level below which no SKU is backordered (Lemma 1).
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 1, pp.20–21; (A.2a), OA p.3

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The workload held in inventory**, `Σᵢ Sᵢ/μᵢ`, for an inventory vector `S`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 1, pp.20–21; (A.2a), OA p.3. -/
noncomputable def Model.invWork {n : ℕ} (M : Model n) (S : Fin n → ℝ) : ℝ :=
  ∑ i, S i / M.mu i

end RepairSched


