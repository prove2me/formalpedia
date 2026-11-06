-- Prove2me | Definitions.Def_SpatialSorting_IsDensity
-- name    : SpatialSorting_IsDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:41.743666+00:00
-- url     : https://prove2.me/theorems/886bf52d-f1c7-4065-b231-169781e668ce
-- title:
--   Density vectors $\Delta_{q-1}$
-- statement:
--   A *density vector* is $\rho=(\rho_0,\dots,\rho_{q-1})$ with every $\rho_i>0$ and $\sum_i\rho_i=1$; that is, $\rho$ lies in the interior $\Delta_{q-1}$ of the $(q-1)$-dimensional probability simplex. It prescribes the colour densities of the free sites.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Fixed magnetization), p. 3 (PDF p. 4)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `ρ ∈ Δ_{q−1}`: `q` positive numbers summing to 1 (the interior of the probability simplex).

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Fixed magnetization), p. 3 (PDF p. 4). -/
def IsDensity {q : ℕ} (ρ : Fin q → ℝ) : Prop := (∀ i, 0 < ρ i) ∧ ∑ i, ρ i = 1

end SpatialSorting


