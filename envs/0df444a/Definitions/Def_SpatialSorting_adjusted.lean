-- Prove2me | Definitions.Def_SpatialSorting_adjusted
-- name    : SpatialSorting_adjusted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:54:28.140878+00:00
-- url     : https://prove2.me/theorems/f31ecb8f-5586-4bd2-88e3-87420d519d47
-- title:
--   The adjusted density $\rho^{\langle\beta\rangle}=\Theta^{-1}\rho$
-- statement:
--   $$\rho^{\langle\beta\rangle}=\Theta^{-1}\rho,$$
--
--   the phase volumes that produce the prescribed colour densities once the thermal defects of each phase are accounted for.
--
--   **Formalization Note** `Matrix.inv` is the zero matrix for a singular matrix; Lemma 5.3 of the mission asserts that $\Theta$ is invertible at the coexistence field.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.3, Eq. (24), p. 29 (PDF p. 30)

import Mathlib
import Definitions.Def_SpatialSorting_theta
open Classical Filter Topology

namespace SpatialSorting

/-- `ρ⟨β⟩ = Θ⁻¹ ρ`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 5.3, Eq. (24), p. 29 (PDF p. 30). -/
noncomputable def adjusted {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ)
    (β : ℝ) (h : Fin q → ℝ) (ρ : Fin q → ℝ) : Fin q → ℝ :=
  Matrix.mulVec (theta A χ β h)⁻¹ ρ

end SpatialSorting


