-- Prove2me | Definitions.Def_MatrixLeeSidford_barrierF
-- name    : MatrixLeeSidford_barrierF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:48.989576+00:00
-- url     : https://prove2.me/theorems/0ad9c385-00e6-43b5-8b25-a750ac884cc7
-- title:
--   Matrix Lee–Sidford barrier $F=\alpha\Phi_p$
-- statement:
--   The **matrix Lee–Sidford barrier** of the pencil is
--   $$
--   F(y)=\alpha\,\Phi_p(y),\qquad s=2\lceil\log(2mn)\rceil,\ p=2s,\ \alpha=10^6s^2 .
--   $$
--   Theorem 2.1 shows that it is a $10^6s^2m$-self-concordant barrier for $\Omega$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 5.1, p.37; Theorem 2.1, p.29

import Mathlib
import Definitions.Def_MatrixLeeSidford_Phi__87229e
import Definitions.Def_MatrixLeeSidford_sParam
import Definitions.Def_MatrixLeeSidford_alphaParam

namespace MatrixLeeSidford

/-- The matrix Lee–Sidford barrier `F := α Φ_p` with `s := 2⌈log(2mn)⌉`, `p = 2s`, `α := 10⁶s²`
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 5.1, p.37; Theorem 2.1, p.29). -/
noncomputable def barrierF {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  alphaParam (sParam m n) * Phi A C (sParam m n) y

end MatrixLeeSidford


