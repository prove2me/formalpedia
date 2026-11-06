-- Prove2me | Definitions.Def_SpatialSorting_Zfix
-- name    : SpatialSorting_Zfix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:48.496522+00:00
-- url     : https://prove2.me/theorems/feaec5f9-2ef7-4b1f-939a-f62e358fdf51
-- title:
--   The fixed-magnetization partition function $Z_{\Lambda^L}(\beta,\rho)$
-- statement:
--   $$Z_{\Lambda^L}(\beta,\rho)=\sum_{\sigma\in\Omega_{\Lambda^L,\rho}}e^{-\beta H_{\Lambda^L}(\sigma)},$$
--
--   the normalising constant of the fixed-magnetization Gibbs distribution at inverse temperature $\beta$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (3), p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_omegaRho
open Classical Filter Topology

namespace SpatialSorting

/-- `Z_{Λ^L}(β, ρ) = Σ_{σ ∈ Ω_{Λ^L,ρ}} e^{−β H(σ)}`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (3), p. 3 (PDF p. 4). -/
noncomputable def Zfix {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (ρ : Fin q → ℝ) (L : ℕ) : ℝ :=
  ∑ σ ∈ omegaRho ρ L, Real.exp (-β * HV A (D L) (extendBy 0 (I L) σ))

end SpatialSorting


