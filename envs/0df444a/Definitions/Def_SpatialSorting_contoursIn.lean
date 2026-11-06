-- Prove2me | Definitions.Def_SpatialSorting_contoursIn
-- name    : SpatialSorting_contoursIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:04.512087+00:00
-- url     : https://prove2.me/theorems/d84d06c0-8a61-42cf-b568-6b80fe89ad22
-- title:
--   All assigned contours supported in a region
-- statement:
--   For a finite region $V$, the finite set of all pairs $(\overline\gamma,\omega_{\overline\gamma})$ with $\overline\gamma\subseteq V$. Every contour whose support lies in $V$ is among them; the polymer families of $V$ are selected from this set.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (helper for $\mathcal P_j(V)$), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- Every pair (support ⊆ `V`, colours on it), as a finite set of `Contour q`; the candidates from which `𝒫_j(V)` is filtered.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (helper for $\mathcal P_j(V)$), p. 17 (PDF p. 18). -/
noncomputable def contoursIn {q : ℕ} [NeZero q] (V : Finset (ℤ × ℤ)) : Finset (Contour q) :=
  (V.powerset ×ˢ (Finset.univ : Finset ({v // v ∈ V} → Fin q))).image
    (fun p => (⟨p.1, fun v => if h : v ∈ p.1 ∧ v ∈ V then p.2 ⟨v, h.2⟩ else 0,
      fun _ hv => dif_neg (fun h => hv h.1)⟩ : Contour q))

end SpatialSorting


