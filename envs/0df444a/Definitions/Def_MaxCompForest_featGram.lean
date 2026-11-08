-- Prove2me | Definitions.Def_MaxCompForest_featGram
-- name    : MaxCompForest_featGram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:09.261365+00:00
-- url     : https://prove2.me/theorems/cdf72cc4-ddef-415e-9fa7-53f993832fd1
-- title:
--   Gram matrix $\mathbf F^{\top}\mathbf F$ of a feature map
-- statement:
--   For feature vectors $\phi_v\in\mathbb R^r$ collected as the columns of $\mathbf F=[\phi_v]_{v}$, the vertex-indexed matrix $\mathbf F^{\top}\mathbf F$, with entries $\langle\phi_u,\phi_v\rangle$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.8) p.16, (E.15) p.40

import Mathlib

namespace MaxCompForest

variable {V : Type*}

/-- **The matrix `𝐅ᵀ𝐅`** where `𝐅 = [ϕ_v]_v` has the feature vectors as columns: its entry at `(u, v)` is
`⟨ϕ_u, ϕ_v⟩`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.8) p.16, (E.15) p.40. -/
noncomputable def featGram {r : ℕ} (φ : V → EuclideanSpace ℝ (Fin r)) : Matrix V V ℝ :=
  Matrix.of fun u v => ∑ i, φ u i * φ v i

end MaxCompForest


