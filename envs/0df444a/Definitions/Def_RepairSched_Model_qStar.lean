-- Prove2me | Definitions.Def_RepairSched_Model_qStar
-- name    : RepairSched_Model_qStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:36.517923+00:00
-- url     : https://prove2.me/theorems/a832ddda-6b4a-43c5-8b9c-997c0ff7cc8a
-- title:
--   The allocation $q^*$ of Definition 2
-- statement:
--   The allocation $q^*$ at workload $w$ and slope $y$ is the allocation without backorders if $w\le\sum_iS_i/\mu_i$, and otherwise the allocation that backorders the tie-broken SKU $\kappa$. The paper's $q^*(w)$ is the value at $y=f'(w)$.
--
--   **Formalization Note** Definition 2 allows any optimal solution of (14). The paper fixes it only by the "specific optimal solution" of OA A.2 and by right-continuity of the drift (OA p.26); this definition spells that choice out.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 1, pp.20–21; Definition 2, p.21; OA A.2, p.2; OA p.26

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_invWork
import Definitions.Def_RepairSched_Model_greedyAlloc
import Definitions.Def_RepairSched_Model_singleBackorderAlloc
import Definitions.Def_RepairSched_Model_kappa

namespace RepairSched

/-- **The allocation `q*`** of Definition 2 at workload `w` and slope `y`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 1, pp.20–21, Definition 2, p.21, OA A.2, p.2, and OA p.26.

If `w ≤ Σᵢ Sᵢ/μᵢ` this is the specific optimal solution of OA A.2; otherwise it is the solution of
Lemma 1 Part ii for the tie-broken `κ`. The paper's `q*(w)` is `qStar S (f′(w)) w`.

**Formalization Note.** Definition 2 allows any optimal solution of (14); the paper fixes it
only by "a specific optimal solution" (p.21) and by right-continuity of its drift (OA p.26).
This definition is that choice, spelled out. -/
noncomputable def Model.qStar {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (y w : ℝ) :
    Fin n → ℝ :=
  if w ≤ M.invWork S then M.greedyAlloc S w else M.singleBackorderAlloc S (M.kappa y) w

end RepairSched


