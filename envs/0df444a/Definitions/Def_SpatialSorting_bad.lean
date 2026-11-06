-- Prove2me | Definitions.Def_SpatialSorting_bad
-- name    : SpatialSorting_bad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:44.748329+00:00
-- url     : https://prove2.me/theorems/995d54a7-e681-412a-8183-183c32c27d83
-- title:
--   Bichromatic sites $\overline\Gamma(\omega)$
-- statement:
--   For an assignment $\omega$ of colours to $\Lambda^\infty$,
--
--   $$\overline\Gamma(\omega)=\{u:\exists v\sim u,\ \omega_u\ne\omega_v\},$$
--
--   the set of sites that participate in a bichromatic edge. A site outside it is *correct*: all its neighbours carry its colour.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SpatialSorting_tri
open Classical Filter Topology

namespace SpatialSorting

/-- `Γ̄(ω) = {u : ∃ v ~ u, ω_u ≠ ω_v}`, the sites of bichromatic edges.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Contours and contour sets), p. 14 (PDF p. 15). -/
def bad {q : ℕ} (ω : ℤ × ℤ → Fin q) : Set (ℤ × ℤ) := {u | ∃ v, tri.Adj u v ∧ ω u ≠ ω v}

end SpatialSorting


