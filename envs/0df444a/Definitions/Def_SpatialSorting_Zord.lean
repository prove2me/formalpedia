-- Prove2me | Definitions.Def_SpatialSorting_Zord
-- name    : SpatialSorting_Zord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:23.980483+00:00
-- url     : https://prove2.me/theorems/78fa3b11-7117-4099-846f-1072edc052fd
-- title:
--   The ordinary partition function $Z_j(\beta,\mathbf h,V)$
-- statement:
--   $$Z_j(\beta,\mathbf h,V)=\sum_{\sigma\in\Omega_j(V)}\exp\bigl(-\beta H_V(\sigma)+\mathbf h\cdot\mathbf n(\sigma)\bigr),$$
--
--   where $H_V$ sums the edges with both endpoints in $V$ and $\mathbf n(\sigma)$ counts all sites of $V$, pinned ones included. For $V=\emptyset$ the value is $1$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_ordinary
open Classical Filter Topology

namespace SpatialSorting

/-- `Z_j(β, h, V) = Σ_{σ ∈ Ω_j(V)} exp(−β H_V(σ) + h · n(σ))`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Partition functions, §3), p. 16 (PDF p. 17). -/
noncomputable def Zord {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ) (h : Fin q → ℝ)
    (j : Fin q) (V : Finset (ℤ × ℤ)) : ℝ :=
  ∑ τ ∈ ordinary j V, Real.exp (-β * HV A V (extendBy j V τ) +
    ∑ i, h i * (nV V (extendBy j V τ) i : ℝ))

end SpatialSorting


