-- Prove2me | Definitions.Def_SpatialSorting_rhoMin
-- name    : SpatialSorting_rhoMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:41.436663+00:00
-- url     : https://prove2.me/theorems/a0cf5444-b612-47e5-9746-9cf1ec1bf8f8
-- title:
--   The smallest density $\rho_{\min}$
-- statement:
--   For a density vector $\rho$, $\rho_{\min}=\min_i\rho_i$. The constant $c_s$ of Theorem 1 depends on $\rho$ only through $\rho_{\min}$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 1, p. 6 (PDF p. 7)

import Mathlib
open Classical Filter Topology

namespace SpatialSorting

/-- `ρ_min = min_i ρ_i`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 1, p. 6 (PDF p. 7). -/
noncomputable def rhoMin {q : ℕ} [NeZero q] (ρ : Fin q → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin q)).inf' Finset.univ_nonempty ρ

end SpatialSorting


