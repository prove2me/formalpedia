-- Prove2me | Definitions.Def_RepairSched_Model_ivpField
-- name    : RepairSched_Model_ivpField
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:58.01143+00:00
-- url     : https://prove2.me/theorems/c73381b6-9072-4e5c-8cf4-33204052a0f6
-- title:
--   Vector field $F(w,g,\gamma)$ of the IVP (A.2)
-- statement:
--   The vector field of the initial value problem (A.2) is
--   $$F(w,g,\gamma)=\frac2\Sigma\Big(\gamma-\theta g-F_0(g)\big(w-\sum_i S_i/\mu_i\big)^+\Big).$$
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (A.3), OA p.3

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_invWork
import Definitions.Def_RepairSched_Model_F0

namespace RepairSched

/-- **The vector field `F`** of the initial value problem (A.2):
`F(w,g,γ) := (2/Σ)(γ − θg − F₀(g)(w − Σᵢ Sᵢ/μᵢ)⁺)`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (A.3), OA p.3. -/
noncomputable def Model.ivpField {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ)
    (w g γ : ℝ) : ℝ :=
  2 / M.Sigma * (γ - M.theta * g - M.F0 g * max (w - M.invWork S) 0)

end RepairSched


