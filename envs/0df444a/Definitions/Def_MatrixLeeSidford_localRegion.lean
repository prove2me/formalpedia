-- Prove2me | Definitions.Def_MatrixLeeSidford_localRegion
-- name    : MatrixLeeSidford_localRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:03.599015+00:00
-- url     : https://prove2.me/theorems/1e4c92de-0117-494d-90b3-3287504403b3
-- title:
--   Symmetrized local region $K=\{h:\|B_h\|_{op}\le1\}$
-- statement:
--   The **symmetrized local region** at the slack $S$ is
--   $$
--   K=\{h\in\mathbb R^m : \|B_h\|_{op}\le1\}.
--   $$
--   At $S=S(y)$, $y\pm h\in\Omega$ for every $h$ in the interior of $K_y$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), p.29 and p.33

import Mathlib
import Definitions.Def_MatrixLeeSidford_Bdir
import Definitions.Def_LiqPremiaEq_opNorm

open Matrix

namespace MatrixLeeSidford

/-- The symmetrized local region `K := {h ∈ ℝᵐ : ‖B_h‖_op ≤ 1}` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.29 and p.33).

**Formalization Note** `‖·‖_op` is the published `LiqPremiaEq.opNorm`, the ℓ²→ℓ² operator norm of
the matrix as a linear map of Euclidean spaces (Section 3.1, p.30). -/
def localRegion {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {h | LiqPremiaEq.opNorm (Bdir A S h) ≤ 1}

end MatrixLeeSidford


