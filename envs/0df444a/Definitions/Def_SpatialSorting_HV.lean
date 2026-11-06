-- Prove2me | Definitions.Def_SpatialSorting_HV
-- name    : SpatialSorting_HV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:40.729504+00:00
-- url     : https://prove2.me/theorems/e0dd995c-b4f3-4f01-a455-615e12f3b827
-- title:
--   The energy $H_V$ of a region
-- statement:
--   For a cost matrix $A$, a finite set $V$ of sites and an assignment $\omega$ of colours,
--
--   $$H_V(\omega)=\sum_{\{u,v\}\in E(V)}A(\omega_u,\omega_v),$$
--
--   the sum over the undirected edges with both endpoints in $V$. Since $A$ has zero diagonal, only bichromatic edges contribute. With $V=D_L$ this is the Hamiltonian $H_{\Lambda^L}$ of Eq. (1), which includes the edges between free and boundary sites; with $V$ a contour support it is the contour cost of Eq. (11).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (1); unnumbered (Partition functions, §3), p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_SpatialSorting_edgesIn
open Classical Filter Topology

namespace SpatialSorting

/-- `H_V(ω) = Σ_{{u,v} ∈ E(V)} A(ω_u, ω_v)`, the energy of the edges with both endpoints in `V`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (1); unnumbered (Partition functions, §3), p. 2 (PDF p. 3). -/
noncomputable def HV {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (V : Finset (ℤ × ℤ))
    (ω : ℤ × ℤ → Fin q) : ℝ :=
  ∑ p ∈ edgesIn V, A (ω p.1) (ω p.2)

end SpatialSorting


