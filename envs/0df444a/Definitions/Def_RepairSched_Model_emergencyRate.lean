-- Prove2me | Definitions.Def_RepairSched_Model_emergencyRate
-- name    : RepairSched_Model_emergencyRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:41.559991+00:00
-- url     : https://prove2.me/theorems/bbf6ad92-9353-41c4-bf69-47ce1409d94d
-- title:
--   The value $c_k\mu_k=\min_i c_i\mu_i$
-- statement:
--   This is the value
--   $$c_k\mu_k=\min_i c_i\mu_i,$$
--   where $k\in\arg\min_i c_i\mu_i$ (p.17). It is the least emergency repair cost per unit of repair time, and it is the other side of the paper's decision rule.
--
--   **Formalization Note** Only the value enters any statement, so no index $k$ is chosen.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), p.17

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The value `ckμk`** with `k ∈ arg minᵢ cᵢμᵢ`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), p.17: "Let k ∈ arg min_{i∈I} ciµi."

**Formalization Note.** Only the value enters any statement, so it is the minimum over the
nonempty SKU set, and no index `k` is chosen. -/
noncomputable def Model.emergencyRate {n : ℕ} [NeZero n] (M : Model n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => M.c i * M.mu i

end RepairSched


