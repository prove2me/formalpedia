-- Prove2me | Definitions.Def_SpatialSorting_Compatible
-- name    : SpatialSorting_Compatible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:57.400201+00:00
-- url     : https://prove2.me/theorems/caed8720-6c09-4377-9b4a-85a2d322b8e1
-- title:
--   Compatible contours
-- statement:
--   Two contours $\gamma,\gamma'$ are compatible when their supports have graph distance at least two: they are disjoint and no edge joins them. Compatibility is geometric and imposes no agreement between the types or labels of the two contours.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, Labels and compatibility), p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_Contour
open Classical Filter Topology

namespace SpatialSorting

/-- Compatibility: `d(γ̄, γ̄') ≥ 2`, that is, disjoint supports with no edge between them.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, Labels and compatibility), p. 15 (PDF p. 16). -/
def Compatible {q : ℕ} [NeZero q] (γ γ' : Contour q) : Prop :=
  ∀ u ∈ γ.support, ∀ v ∈ γ'.support, u ≠ v ∧ ¬ tri.Adj u v

end SpatialSorting


