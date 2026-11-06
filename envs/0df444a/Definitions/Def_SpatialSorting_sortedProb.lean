-- Prove2me | Definitions.Def_SpatialSorting_sortedProb
-- name    : SpatialSorting_sortedProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:49.761532+00:00
-- url     : https://prove2.me/theorems/2d238a96-9b00-4a2f-9a30-b8a5be26a2eb
-- title:
--   The probability $\pi_{\Lambda^L,\beta,\rho}(\mathsf{Sorted}(\alpha,\delta))$
-- statement:
--   $$\pi_{\Lambda^L,\beta,\rho}(\mathsf{Sorted}(\alpha,\delta))=\sum_{\sigma\in\Omega_{\Lambda^L,\rho}:\ \sigma\in\mathsf{Sorted}(\alpha,\delta)}\pi_{\Lambda^L,\beta,\rho}(\sigma),$$
--
--   the Gibbs probability of the Sorted event. Theorem 1 bounds it from below.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (5), p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_SpatialSorting_omegaRho
import Definitions.Def_SpatialSorting_gibbs
import Definitions.Def_SpatialSorting_Sorted
open Classical Filter Topology

namespace SpatialSorting

/-- `π_{Λ^L,β,ρ}(Sorted(α, δ))`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eq. (5), p. 6 (PDF p. 7). -/
noncomputable def sortedProb {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (ρ : Fin q → ℝ) (L : ℕ) (α δ : ℝ) : ℝ :=
  ∑ σ ∈ (omegaRho ρ L).filter (fun σ => Sorted A ρ L α δ σ), gibbs A β ρ L σ

end SpatialSorting


