-- Prove2me | Definitions.Def_SpatialSorting_IsCostMatrix
-- name    : SpatialSorting_IsCostMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:38.506198+00:00
-- url     : https://prove2.me/theorems/c448eb11-bf65-492c-93db-6b2a5388dff5
-- title:
--   Cost matrices $\mathcal A_q$
-- statement:
--   A *cost matrix* is a matrix $A\in\mathbb R^{q\times q}$ that is symmetric, has zeros along its diagonal and has strictly positive entries off the diagonal. $A(i,j)$ is the energy cost of an edge whose endpoints carry colours $i$ and $j$. The set of cost matrices is written $\mathcal A_q$.
--
--   The $q$-state Potts model is $A(i,j)=\mathbb 1_{i\ne j}$; no symmetry among colours and no triangle inequality is assumed.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§1.1), p. 2 (PDF p. 3)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `A ∈ 𝒜_q`: a symmetric real `q × q` matrix with zero diagonal and strictly positive off-diagonal entries.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§1.1), p. 2 (PDF p. 3). -/
def IsCostMatrix {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  A.IsSymm ∧ (∀ i, A i i = 0) ∧ ∀ i j, i ≠ j → 0 < A i j

end SpatialSorting


