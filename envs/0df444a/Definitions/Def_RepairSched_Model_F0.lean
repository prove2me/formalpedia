-- Prove2me | Definitions.Def_RepairSched_Model_F0
-- name    : RepairSched_Model_F0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:13.204073+00:00
-- url     : https://prove2.me/theorems/4b7e8f05-68c8-438b-8e56-9edf5ed37d79
-- title:
--   The function $F_0(g)=\min_i\{b_i\mu_i-\lambda_i g\}$
-- statement:
--   The function
--   $$F_0(g)=\min_i\{b_i\mu_i-\lambda_i g\}$$
--   is continuous, concave, piecewise linear and strictly decreasing. It gives the optimal value of (14) in the backorder region.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (A.3), OA p.3

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The function `F₀`** of (A.3): `F₀(g) := minᵢ {bᵢμᵢ − λᵢg}`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (A.3), OA p.3. -/
noncomputable def Model.F0 {n : ℕ} [NeZero n] (M : Model n) (g : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => M.b i * M.mu i - M.lam i * g

end RepairSched


