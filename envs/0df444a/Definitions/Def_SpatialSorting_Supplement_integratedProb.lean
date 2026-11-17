-- Prove2me | Definitions.Def_SpatialSorting_Supplement_integratedProb
-- name    : SpatialSorting_Supplement_integratedProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:36:44.196869+00:00
-- url     : https://prove2.me/theorems/1e547dd6-aebb-4de8-b2ab-290178a843ab
-- title:
--   $\pi_{\Lambda^L,\beta,\rho}(\mathrm{Integrated}(c,\delta))$
-- statement:
--   For a cost matrix $A$, inverse temperature $\beta$, density vector $\rho$ and side length $L$, the probability of the Integrated event under the fixed-magnetization Gibbs distribution is
--   $$
--   \pi_{\Lambda^L,\beta,\rho}(\mathrm{Integrated}(c,\delta))=\sum_{\sigma\in\Omega_{\Lambda^L,\rho},\ \sigma\in\mathrm{Integrated}(c,\delta)}\frac{e^{-\beta H_{\Lambda^L}(\sigma)}}{Z_{\Lambda^L}(\beta,\rho)} .
--   $$
--
--   This is the quantity bounded in Theorem 2.
--
--   **Formalization Note** Same shape as the base `sortedProb`: a finite sum of the published Gibbs weights `gibbs` over the configurations of `omegaRho` satisfying `Integrated`.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 2, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_SpatialSorting_omegaRho
import Definitions.Def_SpatialSorting_gibbs
import Definitions.Def_SpatialSorting_Supplement_Integrated
open Classical Filter Topology

namespace SpatialSorting.Supplement

/-- `π_{Λ^L,β,ρ}(Integrated(c, δ))`: the fixed-magnetization Gibbs probability of the Integrated event,
the sum of `gibbs A β ρ L σ` over the configurations `σ ∈ Ω_{Λ^L,ρ}` satisfying `Integrated ρ L c δ`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Theorem 2, p. 9 (PDF p. 10).

Formalization Note: same shape as the base `sortedProb`; the Gibbs law is the published `gibbs`. -/
noncomputable def integratedProb {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (β : ℝ)
    (ρ : Fin q → ℝ) (L : ℕ) (c δ : ℝ) : ℝ :=
  ∑ σ ∈ (omegaRho ρ L).filter (fun σ => Integrated ρ L c δ σ), gibbs A β ρ L σ

end SpatialSorting.Supplement


