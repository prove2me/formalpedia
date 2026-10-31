-- Prove2me | Definitions.Def_RepairSched_Model_singleBackorderAlloc
-- name    : RepairSched_Model_singleBackorderAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:32.434982+00:00
-- url     : https://prove2.me/theorems/a5c18842-ca8c-4e92-a77a-be4c310c8b88
-- title:
--   Allocation that backorders one SKU $\kappa$
-- statement:
--   For an index $\kappa$, this is the allocation
--   $$q_i(w)=S_i\ (i\ne\kappa),\qquad q_\kappa(w)=\mu_\kappa\Big(w-\sum_{i\ne\kappa}\frac{S_i}{\mu_i}\Big),$$
--   under which only SKU $\kappa$ is backordered.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 1 Part ii, p.21

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **The allocation of Lemma 1 Part ii** that backorders the single SKU `κ`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 1 Part ii, p.21: `q*ᵢ(w) = Sᵢ` for `i ≠ κ` and
`q*_κ(w) = μ_κ(w − Σ_{i≠κ} Sᵢ/μᵢ)`. -/
noncomputable def Model.singleBackorderAlloc {n : ℕ} (M : Model n) (S : Fin n → ℝ) (κ : Fin n)
    (w : ℝ) : Fin n → ℝ :=
  fun i => if i = κ then M.mu κ * (w - ∑ j ∈ Finset.univ.erase κ, S j / M.mu j) else S i

end RepairSched


