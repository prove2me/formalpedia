-- Prove2me | Definitions.Def_SpatialSorting_Lay
-- name    : SpatialSorting_Lay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:58.145949+00:00
-- url     : https://prove2.me/theorems/c637d3c4-67ae-4e28-8929-ee6fe0427504
-- title:
--   The layers $\mathsf L_r$ of the rhombus
-- statement:
--   For $r\ge0$, $\mathsf L_r=\{v\in D_L: d(v,D_L^c)=r+1\}$, where $d((x,y),D_L^c)=1+\min\{x,y,L-1-x,L-1-y\}$. The wired collar is $B_L=\mathsf L_0\cup\mathsf L_1$; $\mathsf L_0$ is the outer cycle.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Conventions for the scaffold factorization), p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_D
open Classical Filter Topology

namespace SpatialSorting

/-- `L_r = {v ∈ D_L : d(v, D_L^c) = r + 1}`, using `d((x,y), D_L^c) = 1 + min{x, y, L−1−x, L−1−y}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Conventions for the scaffold factorization), p. 19 (PDF p. 20). -/
noncomputable def Lay (r L : ℕ) : Finset (ℤ × ℤ) :=
  (D L).filter (fun v => min (min v.1 v.2) (min ((L : ℤ) - 1 - v.1) ((L : ℤ) - 1 - v.2)) = r)

end SpatialSorting


