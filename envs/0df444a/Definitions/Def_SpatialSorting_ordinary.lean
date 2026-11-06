-- Prove2me | Definitions.Def_SpatialSorting_ordinary
-- name    : SpatialSorting_ordinary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:08.125315+00:00
-- url     : https://prove2.me/theorems/6cd07441-4d39-4c7a-821f-be461d80678e
-- title:
--   The ordinary fixed-collar ensemble $\Omega_j(V)$
-- statement:
--   For a finite region $V$ and a colour $j$,
--
--   $$\Omega_j(V)=\bigl\{\sigma\in\{0,1,\dots,q-1\}^V:\ \sigma(v)=j\ \text{for all }v\text{ with }d(v,V^c)\le2\bigr\},$$
--
--   the fixed-collar ensemble with its two-layer collar pinned to colour $j$ and no contour restriction.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_SpatialSorting_pinned
open Classical Filter Topology

namespace SpatialSorting

/-- `Ω_j(V) = {σ : V → colours : σ(v) = j whenever d(v, V^c) ≤ 2}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17). -/
noncomputable def ordinary {q : ℕ} (j : Fin q) (V : Finset (ℤ × ℤ)) :
    Finset ({v // v ∈ V} → Fin q) :=
  Finset.univ.filter (fun τ => ∀ v : {v // v ∈ V}, v.1 ∈ pinned V → τ v = j)

end SpatialSorting


