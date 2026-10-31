-- Prove2me | Definitions.Def_RepairSched_Model_backorderRatio
-- name    : RepairSched_Model_backorderRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:46.173994+00:00
-- url     : https://prove2.me/theorems/7a6bfc9e-c525-47cd-954d-18f00ee26f31
-- title:
--   The value $b_j\mu_j/\lambda_j=\min_i b_i\mu_i/\lambda_i$
-- statement:
--   This is the value
--   $$\frac{b_j\mu_j}{\lambda_j}=\min_i \frac{b_i\mu_i}{\lambda_i},$$
--   where $j\in\arg\min_i b_i\mu_i/\lambda_i$ is the index of (11). It is the least backorder saving per unit of repair time, and it is one side of the paper's decision rule.
--
--   **Formalization Note** Only the value enters any statement, so no index $j$ is chosen.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (11), p.18

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The value `bjμj/λj`** with `j ∈ arg minᵢ bᵢμᵢ/λᵢ`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (11), p.18.

**Formalization Note.** Only the value enters any statement, so it is the minimum over the
nonempty SKU set, and no index `j` is chosen. -/
noncomputable def Model.backorderRatio {n : ℕ} [NeZero n] (M : Model n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => M.b i * M.mu i / M.lam i

end RepairSched


