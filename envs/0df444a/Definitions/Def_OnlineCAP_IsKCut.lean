-- Prove2me | Definitions.Def_OnlineCAP_IsKCut
-- name    : OnlineCAP_IsKCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:50.210479+00:00
-- url     : https://prove2.me/theorems/fd8f9f15-1fe7-45b9-b7eb-ea64a45daf24
-- title:
--   k-cut (minimum cut)
-- statement:
--   A vertex set $C$ with $\emptyset\neq C\neq V$ is a **$k$-cut** of the multigraph if $|\delta_E(C)|=k$. In a $k$-edge-connected graph the $k$-cuts are its minimum cuts; they are the requests of online connectivity augmentation with cut arrivals.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2, p.9

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut

namespace OnlineCAP

/-- **k-cut (minimum cut).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2, p.9 (PDF p.9): "A cut C is a minimum cut (or k-cut) if
|δE(C)| = k."

`C` is a k-cut when `∅ ≠ C ≠ V` and exactly `k` edges have exactly one end in `C`. In a
k-edge-connected graph these are the minimum cuts. -/
def IsKCut {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ)
    (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧ C ≠ Finset.univ ∧ (edgeCut ends C).card = k

end OnlineCAP


