-- Prove2me | Definitions.Def_MaxCompForest_compMu
-- name    : MaxCompForest_compMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:05.896576+00:00
-- url     : https://prove2.me/theorems/2fa9d19a-f7d8-47e4-93df-9d3494b9fc61
-- title:
--   Component moment $\mu_C$
-- statement:
--   $\mu_C=\sum_{v\in V(C)}d_v\phi_v$, for vertex masses $d$ and feature vectors $\phi_v\in\mathbb R^r$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.6), p.16

import Mathlib
import Definitions.Def_MaxCompForest_compVerts
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **The first moment** `μ_C = ∑_{v ∈ V(C)} d_v ϕ_v` of a component.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.6), p.16. -/
noncomputable def compMu {r : ℕ} (G : WGraph V E) (F : Finset E) (d : V → ℝ)
    (φ : V → EuclideanSpace ℝ (Fin r)) (C : ContractV G F) : Fin r → ℝ :=
  fun i => ∑ v ∈ compVerts G F C, d v * φ v i

end MaxCompForest


