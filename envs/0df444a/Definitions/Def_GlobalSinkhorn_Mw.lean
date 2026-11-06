-- Prove2me | Definitions.Def_GlobalSinkhorn_Mw
-- name    : GlobalSinkhorn_Mw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:25.07821+00:00
-- url     : https://prove2.me/theorems/865c011d-4841-4fe1-908e-ae5f09b9386f
-- title:
--   The matrix $M(w)=\operatorname{diag}((Sw)^{-1})\,S\,\operatorname{diag}(w)$
-- statement:
--   Let $S$ be a nonnegative doubly stochastic $n\times n$ matrix and $w\in\mathbb R^n_{>0}$. Define
--   $$
--   M(w)=\operatorname{diag}\big((Sw)^{-1}\big)\,S\,\operatorname{diag}(w),\qquad (M(w))_{ij}=\frac{S_{ij}w_j}{(Sw)_i},
--   $$
--   with componentwise reciprocal. $M(w)$ is row-stochastic, and every even Sinkhorn–Knopp iterate has this form: $A^{(2t)}=M(w_t)$ for a suitable sequence $w_t$ (Eq. (34)).
--
--   **Formalization Note** Lean's total inverse is used for $(Sw)_i^{-1}$; for $w>0$ and doubly stochastic $S$ every $(Sw)_i$ is positive (p.15), so it never yields the junk value.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Eq. (22), p.15

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- `M(w) = diag((S w)⁻¹) S diag(w)`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Eq. (22), p.15.

**Formalization Note.** Reciprocals are componentwise. For `w > 0` and doubly stochastic `S`,
`(S w) i > 0`, so Lean's total inverse never fires. -/
noncomputable def Mw {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ((S *ᵥ w) i)⁻¹) * S * Matrix.diagonal w

end GlobalSinkhorn


