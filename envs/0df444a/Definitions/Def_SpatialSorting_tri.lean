-- Prove2me | Definitions.Def_SpatialSorting_tri
-- name    : SpatialSorting_tri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:35.270468+00:00
-- url     : https://prove2.me/theorems/44570ff0-f715-44fe-a07c-9149058ba9af
-- title:
--   The infinite triangular lattice $\Lambda^\infty$
-- statement:
--   The infinite triangular lattice $\Lambda^\infty$ has vertex set $\mathbb Z^2$, and two sites $u,v$ are adjacent when
--
--   $$v-u\in\{\pm(1,0),\ \pm(0,1),\ \pm(1,-1)\}.$$
--
--   Embedding $(x,y)$ at $(x+y/2,\sqrt3\,y/2)$ gives the usual triangular lattice, in which every site has six neighbours. All graph notions of the mission (contours, components, distances, collars) refer to this graph.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- The infinite triangular lattice `Λ^∞` on `ℤ²`: `u ~ v` iff `v − u ∈ {±(1,0), ±(0,1), ±(1,−1)}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (The domain), p. 3 (PDF p. 4). -/
def tri : SimpleGraph (ℤ × ℤ) where
  Adj u v := (v.1 - u.1 = 1 ∧ v.2 - u.2 = 0) ∨ (v.1 - u.1 = -1 ∧ v.2 - u.2 = 0) ∨
    (v.1 - u.1 = 0 ∧ v.2 - u.2 = 1) ∨ (v.1 - u.1 = 0 ∧ v.2 - u.2 = -1) ∨
    (v.1 - u.1 = 1 ∧ v.2 - u.2 = -1) ∨ (v.1 - u.1 = -1 ∧ v.2 - u.2 = 1)
  symm := ⟨fun _ _ h => by omega⟩
  loopless := ⟨fun _ h => by omega⟩

end SpatialSorting


