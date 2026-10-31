-- Prove2me | Definitions.Def_RepairSched_Model_backorderRate
-- name    : RepairSched_Model_backorderRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:50:00.379714+00:00
-- url     : https://prove2.me/theorems/da93e0fd-afd1-489a-ac65-edeb87c7ce37
-- title:
--   Drift $\beta(w)=\sum_i(\lambda_i/\mu_i)(q^*_i(w)-S_i)^+$
-- statement:
--   This is the rate at which the workload drains through abandonment of backordered demand under $q^*$:
--   $$\beta(w)=\sum_i\frac{\lambda_i}{\mu_i}\big(q^*_i(w)-S_i\big)^+.$$
--   By Lemma 1, $\beta(w)=\lambda_{\kappa(w)}(w-\sum_iS_i/\mu_i)^+$, which jumps upward wherever $\kappa$ changes.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Definition 5 C1, p.25; OA p.25

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_qStar

namespace RepairSched

/-- **The drift `β(w) = Σᵢ (λᵢ/μᵢ)(q*ᵢ(w) − Sᵢ)⁺`** removed from the workload under `q*`, for the
function `f`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Definition 5 C1, p.25, and OA p.25 (PDF p.65), where it is called `β^(λ,μ,s)`. -/
noncomputable def Model.backorderRate {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ)
    (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∑ i, M.lam i / M.mu i * max (M.qStar S (deriv f w) w i - S i) 0

end RepairSched


