-- Prove2me | Definitions.Def_SpatialSorting_gibbs
-- name    : SpatialSorting_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:24.775667+00:00
-- url     : https://prove2.me/theorems/6d838b7b-965c-4200-a63d-a2fd79e2e628
-- title:
--   The F-GPM Gibbs distribution $\pi_{\Lambda^L,\beta,\rho}$
-- statement:
--   The fixed-magnetization Generalized Potts Model (F-GPM) assigns to $\sigma\in\Omega_{\Lambda^L,\rho}$ the probability
--
--   $$\pi_{\Lambda^L,\beta,\rho}(\sigma)=\frac{e^{-\beta H_{\Lambda^L}(\sigma)}}{Z_{\Lambda^L}(\beta,\rho)} .$$
--
--   **Formalization Note** The function is defined on every configuration; probabilities of events are sums over the events intersected with $\Omega_{\Lambda^L,\rho}$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (3), p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_Zfix
open Classical Filter Topology

namespace SpatialSorting

/-- `π_{Λ^L,β,ρ}(σ) = e^{−β H(σ)} / Z_{Λ^L}(β, ρ)`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (3), p. 3 (PDF p. 4). -/
noncomputable def gibbs {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (ρ : Fin q → ℝ) (L : ℕ) (σ : Coloring q L) : ℝ :=
  Real.exp (-β * HV A (D L) (extendBy 0 (I L) σ)) / Zfix A β ρ L

end SpatialSorting


