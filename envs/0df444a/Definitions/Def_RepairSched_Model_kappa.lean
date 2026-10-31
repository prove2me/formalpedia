-- Prove2me | Definitions.Def_RepairSched_Model_kappa
-- name    : RepairSched_Model_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:41.262668+00:00
-- url     : https://prove2.me/theorems/04cef08f-fc25-4e1d-ac19-3f4cde3103f0
-- title:
--   The SKU $\kappa$ at slope $y$
-- statement:
--   This is the unique index with the tie-breaking property at slope $y$. The paper's $\kappa(w)$ is the value at $y=f'(w)$.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 1 Part ii, p.21; OA p.26 (PDF p.66)

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_IsKappa

namespace RepairSched

/-- **The SKU `κ` at slope `y`**: the unique index satisfying `IsKappa`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 1 Part ii, p.21, and OA p.26 (PDF p.66).

**Formalization Note.** Finitely many indices with a strict lexicographic order give existence
and uniqueness of such an index, so `Classical.epsilon` picks it for every `y`. -/
noncomputable def Model.kappa {n : ℕ} [NeZero n] (M : Model n) (y : ℝ) : Fin n :=
  Classical.epsilon (M.IsKappa y)

end RepairSched


