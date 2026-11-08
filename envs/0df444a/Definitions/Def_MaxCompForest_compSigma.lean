-- Prove2me | Definitions.Def_MaxCompForest_compSigma
-- name    : MaxCompForest_compSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:59.840259+00:00
-- url     : https://prove2.me/theorems/87678f5b-1161-4444-8037-694732b8a075
-- title:
--   Component covariance $\Sigma_C$
-- statement:
--   $$
--   \Sigma_C=\sum_{v\in V(C)}d_v\phi_v\phi_v^{\top}-\frac{\mu_C\mu_C^{\top}}{m_C},
--   $$
--   which measures the weighted variation of the feature vectors of $C$ around their mean. It is positive semidefinite.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.6), p.16

import Mathlib
import Definitions.Def_MaxCompForest_compMass
import Definitions.Def_MaxCompForest_compMu
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **The component covariance** `Σ_C = ∑_{v ∈ V(C)} d_v ϕ_v ϕ_vᵀ − μ_C μ_Cᵀ / m_C`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.6), p.16. Every use has positive masses, so `m_C > 0`. -/
noncomputable def compSigma {r : ℕ} (G : WGraph V E) (F : Finset E) (d : V → ℝ)
    (φ : V → EuclideanSpace ℝ (Fin r)) (C : ContractV G F) : Matrix (Fin r) (Fin r) ℝ :=
  (∑ v ∈ compVerts G F C, d v • Matrix.vecMulVec (fun i => φ v i) (fun i => φ v i)) -
    (compMass G F d C)⁻¹ • Matrix.vecMulVec (compMu G F d φ C) (compMu G F d φ C)

end MaxCompForest


