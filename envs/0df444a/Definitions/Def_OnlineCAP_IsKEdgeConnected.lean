-- Prove2me | Definitions.Def_OnlineCAP_IsKEdgeConnected
-- name    : OnlineCAP_IsKEdgeConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:39.89312+00:00
-- url     : https://prove2.me/theorems/e912686f-49a5-41f2-a3bf-168ac1b3ccc5
-- title:
--   k-edge-connected multigraph
-- statement:
--   A multigraph on the vertex set $V$ is **$k$-edge-connected** if
--
--   $$|\delta_E(C)|\ge k\qquad\text{for every } C\subseteq V \text{ with } \emptyset\neq C\neq V .$$
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2, p.9

import Mathlib
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut

namespace OnlineCAP

/-- **k-edge-connected multigraph.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2, p.9 (PDF p.9): "we are given a k-edge-connected
graph G = (V, E) with |V| = n … Since G is k-edge-connected, every cut C has |δE(C)| ≥ k."

Every vertex set `C` with `∅ ≠ C ≠ V` has at least `k` edges with exactly one end in `C`. -/
def IsKEdgeConnected {n : ℕ} {E : Type} [Fintype E] (ends : E → Sym2 (Fin n)) (k : ℕ) : Prop :=
  ∀ C : Finset (Fin n), C.Nonempty → C ≠ Finset.univ → k ≤ (edgeCut ends C).card

end OnlineCAP


