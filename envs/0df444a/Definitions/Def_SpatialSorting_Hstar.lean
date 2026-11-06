-- Prove2me | Definitions.Def_SpatialSorting_Hstar
-- name    : SpatialSorting_Hstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:57.28994+00:00
-- url     : https://prove2.me/theorems/24d47012-61eb-4ceb-8719-684f663ee5f4
-- title:
--   The minimum energy $H_*(L,\rho)$
-- statement:
--   $$H_*(L,\rho)=\min_{\eta\in\Omega_{\Lambda^L,\rho}}H_{\Lambda^L}(\eta),$$
--
--   the smallest energy of a configuration with the prescribed colour counts. It is the benchmark of the Sorted event; by Lemma 5.8 it is of order $L$.
--
--   **Formalization Note** A minimum over a finite set; the set is nonempty for every density vector, and the value $0$ is used only for an empty set.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 1.1, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_omegaRho
open Classical Filter Topology

namespace SpatialSorting

/-- `H_*(L, ρ) = min_{η ∈ Ω_{Λ^L,ρ}} H(η)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 1.1, p. 6 (PDF p. 7). -/
noncomputable def Hstar {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ)
    (ρ : Fin q → ℝ) (L : ℕ) : ℝ :=
  if h : (omegaRho ρ L).Nonempty then
    (omegaRho ρ L).inf' h (fun σ => HV A (D L) (extendBy 0 (I L) σ)) else 0

end SpatialSorting


