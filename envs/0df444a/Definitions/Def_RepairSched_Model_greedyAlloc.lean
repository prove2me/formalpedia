-- Prove2me | Definitions.Def_RepairSched_Model_greedyAlloc
-- name    : RepairSched_Model_greedyAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:18.346579+00:00
-- url     : https://prove2.me/theorems/8923a579-69a6-46c6-a16e-b0ce81adcb41
-- title:
--   Allocation without backorders, OA A.2
-- statement:
--   For $w\le\sum_iS_i/\mu_i$, take the least $m$ with $\sum_{i\le m}S_i/\mu_i\ge w$ and set $q_i(w)=S_i$ for $i<m$, $q_m(w)=\mu_m\big(w-\sum_{i<m}S_i/\mu_i\big)$ and $q_i(w)=0$ for $i>m$. This is the specific optimal solution the paper gives in this case.
--
--   **Formalization Note** The three cases are the single formula $q_i(w)=\mu_i\min\big(S_i/\mu_i,(w-\sum_{j<i}S_j/\mu_j)^+\big)$, which needs no choice of $m$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), OA A.2, p.2 (PDF p.42)

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The allocation of Lemma 1 Part i without backorders**, for `w ≤ Σᵢ Sᵢ/μᵢ`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), OA A.2, p.2 (PDF p.42): with `m` the least index such that `Σ_{i≤m} Sᵢ/μᵢ ≥ w`,
`qᵢ(w) = Sᵢ` for `i < m`, `q_m(w) = μ_m(w − Σ_{i<m} Sᵢ/μᵢ)`, `qᵢ(w) = 0` for `i > m`.

**Formalization Note.** The three cases are the single formula
`qᵢ(w) = μᵢ min(Sᵢ/μᵢ, (w − Σ_{j<i} Sⱼ/μⱼ)⁺)`, which needs no choice of `m`. For the least such
`m`, the second argument exceeds `Sᵢ/μᵢ` for `i < m`, lies in `[0, S_m/μ_m]` for `i = m`, and is
`0` for `i > m`. -/
noncomputable def Model.greedyAlloc {n : ℕ} (M : Model n) (S : Fin n → ℝ) (w : ℝ) :
    Fin n → ℝ :=
  fun i => M.mu i * min (S i / M.mu i) (max (w - ∑ j ∈ Finset.Iio i, S j / M.mu j) 0)

end RepairSched


