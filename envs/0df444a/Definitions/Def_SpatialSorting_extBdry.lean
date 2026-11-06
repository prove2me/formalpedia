-- Prove2me | Definitions.Def_SpatialSorting_extBdry
-- name    : SpatialSorting_extBdry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:56.288547+00:00
-- url     : https://prove2.me/theorems/d03ea9d2-f3e9-4afd-bc22-c6dffb6254a4
-- title:
--   The exterior boundary $\partial_{\rm ext}V$
-- statement:
--   $\partial_{\rm ext}V=\{y\notin V:\ d(y,V)=1\}$, the sites outside $V$ adjacent to $V$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_nbhd
open Classical Filter Topology

namespace SpatialSorting

/-- `∂_ext V = {y ∉ V : d(y, V) = 1}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 4.6, p. 27 (PDF p. 28). -/
noncomputable def extBdry (V : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (nbhd V).filter (fun y => y ∉ V ∧ ∃ v ∈ V, tri.Adj y v)

end SpatialSorting


