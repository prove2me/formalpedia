-- Prove2me | Definitions.Def_SpatialSorting_ZresFix
-- name    : SpatialSorting_ZresFix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:12.481393+00:00
-- url     : https://prove2.me/theorems/d590b519-7037-4eb9-aaa8-44135d197025
-- title:
--   The restricted fixed-count partition function $Z^L_{j,\mathbf m}(V)$
-- statement:
--   For a count vector $\mathbf m$, $\Omega^L_{j,\mathbf m}(V)$ is the set of $\sigma\in\Omega^L_j(V)$ with $\mathbf n(\sigma)=\mathbf m$, and $Z^L_{j,\mathbf m}(V)$ is its contribution to $Z^L_j(V)$:
--
--   $$Z^L_{j,\mathbf m}(\beta,\mathbf h,V)=\sum_{\sigma\in\Omega^L_{j,\mathbf m}(V)}e^{-\beta H_V(\sigma)+\mathbf h\cdot\mathbf m}.$$
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_restricted
open Classical Filter Topology

namespace SpatialSorting

/-- `Z^L_{j,m}(V)`: the contribution to `Z^L_j(V)` of `Ω^L_{j,m}(V) = {σ ∈ Ω^L_j(V) : n(σ) = m}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19). -/
noncomputable def ZresFix {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (h : Fin q → ℝ) (j : Fin q) (V : Finset (ℤ × ℤ)) (m : Fin q → ℕ) : ℝ :=
  ∑ τ ∈ (restricted j V).filter (fun τ => ∀ i, nV V (extendBy j V τ) i = m i),
    Real.exp (-β * HV A V (extendBy j V τ) + ∑ i, h i * (m i : ℝ))

end SpatialSorting


