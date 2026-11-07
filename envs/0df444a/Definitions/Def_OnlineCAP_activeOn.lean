-- Prove2me | Definitions.Def_OnlineCAP_activeOn
-- name    : OnlineCAP_activeOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:39.838761+00:00
-- url     : https://prove2.me/theorems/e1cdd0e3-6748-411a-9fa6-a2569e5f60ce
-- title:
--   Active copies A(S) of a region
-- statement:
--   For a region $S$, $A(S)=A\cap\pi^{-1}(S)$ is the set of active copies whose physical parent lies in $S$.
--
--   **Formalization Note** A region enters through its trace $S\cap P$, a subset of $P$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.16

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_zvec
import Definitions.Def_OnlineCAP_acount
import Definitions.Def_OnlineCAP_active

namespace OnlineCAP

/-- **Active copies of a region, `A(S)`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, p.16 (PDF p.16): "For any subset S ⊆ R2,
let A^t(S) := A^t ∩ π^{−1}(S) denote the set of active copies of points in S at time step t."

For a set `R` of points of `P`, `activeOn P x R` is the set of active copies whose parent lies in
`R`.

**Formalization Note.** A region of the plane enters through its trace on `P` (a `Set ↥P`). -/
noncomputable def activeOn (P : Finset (ℝ × ℝ)) (x : ↥P → ℝ) (R : Set ↥P) :
    Finset (VirtualPt P) := by
  classical
  exact (active P x).filter (fun e => e.1 ∈ R)

end OnlineCAP


