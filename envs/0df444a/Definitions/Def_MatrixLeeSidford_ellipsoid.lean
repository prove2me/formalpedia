-- Prove2me | Definitions.Def_MatrixLeeSidford_ellipsoid
-- name    : MatrixLeeSidford_ellipsoid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:08.003289+00:00
-- url     : https://prove2.me/theorems/9ce692d9-c1b0-473b-80ec-29d90ebbd8c2
-- title:
--   Ellipsoid $E_G=\{G^{1/2}z:\|z\|_2\le1\}$
-- statement:
--   For a positive semidefinite $m\times m$ matrix $G$,
--   $$
--   E_G=\{G^{1/2}z : z\in\mathbb R^m,\ \|z\|_2\le1\},
--   $$
--   with $G^{1/2}$ the positive semidefinite square root. Its volume is proportional to $\sqrt{\det G}$, and $cE_G$ denotes the scaled set.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), p.29; Section 4.1, p.32

import Mathlib
import Definitions.Def_MatrixLeeSidford_matRpow

open Matrix

namespace MatrixLeeSidford

/-- The ellipsoid `E_G := {G^{1/2} z : ‖z‖₂ ≤ 1}` of a weight `G ⪰ 0` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.29 and
Section 4.1, p.32).

**Formalization Note** `G^{1/2}` is the positive semidefinite square root `matRpow (1/2) G`;
`‖z‖` is the Euclidean norm of `EuclideanSpace ℝ (Fin m)`. A scaled ellipsoid `c E_G` is the
pointwise scalar multiple `c • ellipsoid G`. -/
def ellipsoid {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {h | ∃ z : EuclideanSpace ℝ (Fin m), ‖z‖ ≤ 1 ∧ h = Matrix.toEuclideanLin (matRpow (1 / 2) G) z}

end MatrixLeeSidford


