-- Prove2me | Definitions.Def_MaxCompForest_detScore
-- name    : MaxCompForest_detScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:32.368834+00:00
-- url     : https://prove2.me/theorems/bdcc158f-067e-43db-8f4d-d7e0c6658061
-- title:
--   Item score $f_x(B)=p_x\det(B+\sum_i d_{x,i}a_ia_i^{\top})$
-- statement:
--   For rational columns $a_1,\dots,a_m\in\mathbb Q^{D}$, a scalar $p$, masses $d_1,\dots,d_m$ and a real $D\times D$ matrix $B$,
--   $$
--   f(B)=p\det\Big(B+\sum_{i=1}^m d_ia_ia_i^{\top}\Big).
--   $$
--   The determinant is affine in each mass separately, which is what makes a small support possible.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.4, p.20

import Mathlib

namespace MaxCompForest

/-- **The item score** `f_x(B) = p_x det(B + ∑_i d_{x,i} a_i a_iᵀ)`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 3.4, p.20. -/
noncomputable def detScore {m D : ℕ} (a : Fin m → Fin D → ℚ) (p : ℚ) (d : Fin m → ℚ)
    (B : Matrix (Fin D) (Fin D) ℝ) : ℝ :=
  (p : ℝ) * Matrix.det (B + ∑ i, (d i : ℝ) • Matrix.vecMulVec (fun l => (a i l : ℝ)) (fun l => (a i l : ℝ)))

end MaxCompForest


