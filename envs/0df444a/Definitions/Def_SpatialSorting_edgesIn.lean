-- Prove2me | Definitions.Def_SpatialSorting_edgesIn
-- name    : SpatialSorting_edgesIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:40.710078+00:00
-- url     : https://prove2.me/theorems/db41c767-027b-467c-95df-cc5753e3cb21
-- title:
--   The edges inside a region
-- statement:
--   For a finite set $V$ of sites, $E(V)$ is the set of edges of the triangular lattice with both endpoints in $V$. Each undirected edge $\{u,v\}$ is listed exactly once, as the ordered pair $(u,v)$ with $v-u\in\{(1,0),(0,1),(1,-1)\}$.
--
--   **Formalization Note** Listing each edge once matters: the Hamiltonian is a sum over undirected edges, and a sum over ordered adjacent pairs would double it.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (1), p. 2 (PDF p. 3)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- The edges of `Λ^∞` with both endpoints in `V`, each listed once as an ordered pair `(u, u + d)` with `d ∈ {(1,0), (0,1), (1,−1)}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (1), p. 2 (PDF p. 3). -/
noncomputable def edgesIn (V : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (V ×ˢ V).filter (fun p => p.2 - p.1 = (1, 0) ∨ p.2 - p.1 = (0, 1) ∨ p.2 - p.1 = (1, -1))

end SpatialSorting


