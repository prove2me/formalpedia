-- Prove2me | Definitions.Def_SpatialSorting_IsMinimal
-- name    : SpatialSorting_IsMinimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:54.216422+00:00
-- url     : https://prove2.me/theorems/5a7a76f2-daa4-4fe5-baa3-646c82ecd45b
-- title:
--   Minimal-cost configurations $\sigma^L_\rho$
-- statement:
--   $\sigma\in\Omega^L_\rho$ is a minimal-cost configuration of $\Lambda^L$ with density $\rho$ if
--
--   $$H(\sigma)\le\min_{\sigma'\in\Omega^L_\rho}H(\sigma').$$
--
--   The paper writes $\sigma^L_\rho$ for an arbitrary but fixed one; the optimal contour set is $\mathcal O_\beta=\Gamma(\sigma^L_{\rho^{\langle\beta\rangle}})$ (Definition 5.6), and every bound of the paper holds for any choice.
--
--   **Formalization Note** Stated for an arbitrary vector $\rho'$, so that it applies at the adjusted density.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 5.5, p. 30 (PDF p. 31)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_omegaRho
open Classical Filter Topology

namespace SpatialSorting

/-- Definition 5.5: `σ ∈ Ω^L_ρ` with `H(σ) ≤ min_{σ' ∈ Ω^L_ρ} H(σ')`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Definition 5.5, p. 30 (PDF p. 31). -/
def IsMinimal {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (ρ : Fin q → ℝ) (L : ℕ)
    (σ : Coloring q L) : Prop :=
  σ ∈ omegaRho ρ L ∧ ∀ η ∈ omegaRho ρ L,
    HV A (D L) (extendBy 0 (I L) σ) ≤ HV A (D L) (extendBy 0 (I L) η)

end SpatialSorting


