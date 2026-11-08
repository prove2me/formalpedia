-- Prove2me | Definitions.Def_MaxCompForest_ratFeat
-- name    : MaxCompForest_ratFeat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:12.360319+00:00
-- url     : https://prove2.me/theorems/6197e9f2-2019-40fd-8c41-3e742b739762
-- title:
--   Feature map of a rational factor
-- statement:
--   For a rational matrix $\mathbf F\in\mathbb Q^{r\times V}$, the map sending $v$ to its column $\phi_v$, viewed in $\mathbb R^r$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.8) p.16, Theorem F.1 p.42

import Mathlib

namespace MaxCompForest

variable {V : Type*}

/-- **The feature map of a rational factor** `𝐅 ∈ ℚ^{r × V}`: `ϕ_v` is the column of `v`, in `ℝ^r`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.8) p.16, Theorem F.1 p.42, Lemma 3.5 p.22. -/
noncomputable def ratFeat {r : ℕ} (F : Fin r → V → ℚ) : V → EuclideanSpace ℝ (Fin r) :=
  fun v => WithLp.toLp 2 fun i => (F i v : ℝ)

end MaxCompForest


