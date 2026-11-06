-- Prove2me | Definitions.Def_SpatialSorting_IsLabeling
-- name    : SpatialSorting_IsLabeling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:00.994213+00:00
-- url     : https://prove2.me/theorems/a407eb48-46ef-483c-9f76-67cbee349385
-- title:
--   Scaffold labels (W3)
-- statement:
--   A labelling of the complementary components of $\mathcal S$ assigns to each component $V_k$ a colour $j_k$ such that $\omega_{\mathcal S}(s)=j_k$ for every $s\in\overline{\mathcal S}$ adjacent to $V_k$, and $j_0=0$, where $V_0$ is the component containing $\mathsf L_0$.
--
--   **Formalization Note** "$V_0$ contains $\mathsf L_0$" is written as "$V$ meets $\mathsf L_0$"; for a scaffold $\mathsf L_0$ is connected and disjoint from $\overline{\mathcal S}$, so exactly one component meets it.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8 (W3), p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_Lay
import Definitions.Def_SpatialSorting_comps
open Classical Filter Topology

namespace SpatialSorting

/-- Condition (W3): `lab` gives each component `V_k` a label `j_k` equal to `ω_𝒮(s)` for every `s ∈ 𝒮̄` adjacent to `V_k`, with `j_0 = 0` on the component meeting `L_0`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.8 (W3), p. 20 (PDF p. 21). -/
def IsLabeling {q : ℕ} [NeZero q] (L : ℕ) (S : Finset (Contour q))
    (lab : Finset (ℤ × ℤ) → Fin q) : Prop :=
  (∀ V ∈ comps L S, ∀ γ ∈ S, ∀ s ∈ γ.support, (∃ v ∈ V, tri.Adj s v) → γ.color s = lab V) ∧
    ∀ V ∈ comps L S, (V ∩ Lay 0 L).Nonempty → lab V = 0

end SpatialSorting


