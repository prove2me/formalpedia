-- Prove2me | Definitions.Def_SpatialSorting_Zres
-- name    : SpatialSorting_Zres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:04.847474+00:00
-- url     : https://prove2.me/theorems/ff0d33de-24ee-401d-b03b-17d0ccc94db9
-- title:
--   The restricted partition function $Z^L_j(\beta,\mathbf h,V)$
-- statement:
--   $$Z^L_j(\beta,\mathbf h,V)=\sum_{\sigma\in\Omega^L_j(V)}\exp\bigl(-\beta H_V(\sigma)+\mathbf h\cdot\mathbf n(\sigma)\bigr),$$
--
--   the partition function of the restricted fixed-collar ensemble of Definition 3.5.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_restricted
open Classical Filter Topology

namespace SpatialSorting

/-- `Z^L_j(β, h, V) = Σ_{σ ∈ Ω^L_j(V)} exp(−β H_V(σ) + h · n(σ))`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 3.5, p. 18 (PDF p. 19). -/
noncomputable def Zres {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (h : Fin q → ℝ) (j : Fin q) (V : Finset (ℤ × ℤ)) : ℝ :=
  ∑ τ ∈ restricted j V, Real.exp (-β * HV A V (extendBy j V τ) +
    ∑ i, h i * (nV V (extendBy j V τ) i : ℝ))

end SpatialSorting


