-- Prove2me | Definitions.Def_RepairSched_Model_allocCost
-- name    : RepairSched_Model_allocCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:17.693528+00:00
-- url     : https://prove2.me/theorems/115d2a9e-88ce-4b08-ad0d-0c54bf3a9728
-- title:
--   Objective of the allocation problem (14)
-- statement:
--   At slope $y$, the objective of the allocation problem is
--   $$\sum_i\Big(b_i-\frac{\lambda_i}{\mu_i}y\Big)(q_i-S_i)^+.$$
--   In the Bellman system and in (14), $y=f'(w)$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (13a), p.19; (14), p.20

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The objective of the allocation problem (14)** at slope `y`:
`Σᵢ (bᵢ − (λᵢ/μᵢ) y) (qᵢ − Sᵢ)⁺`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (13a) p.19 and (14) p.20, where `y = f′(w)`. -/
noncomputable def Model.allocCost {n : ℕ} (M : Model n) (S : Fin n → ℝ) (y : ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ i, (M.b i - M.lam i / M.mu i * y) * max (q i - S i) 0

end RepairSched


