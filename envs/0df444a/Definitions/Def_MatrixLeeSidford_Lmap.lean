-- Prove2me | Definitions.Def_MatrixLeeSidford_Lmap
-- name    : MatrixLeeSidford_Lmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:52.938575+00:00
-- url     : https://prove2.me/theorems/5c2117e1-05cf-41b3-af20-457c2db23470
-- title:
--   Sum-of-squares map $L(G)=\sum_{i,j}G_{ij}B_iB_j$
-- statement:
--   For an $m\times m$ weight matrix $G$ define the $n\times n$ matrix
--   $$
--   L(G)=\sum_{i,j=1}^m G_{ij}\,B_iB_j ,
--   $$
--   with $B_i$ the normalized constraint matrices at the slack $S$ ($L_y=L_{S(y)}$). For $G\succeq0$, $L(G)$ dominates the squares of all $B_h$ with $h$ in the ellipsoid $E_G$ (Lemma 4.1).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Eq. (4.5), p.33; Section 5.1, p.37

import Mathlib
import Definitions.Def_MatrixLeeSidford_normB

open Matrix

namespace MatrixLeeSidford

/-- The linear map `L(G) := ∑_{i,j} Gᵢⱼ Bᵢ Bⱼ` from `m × m` weights to `n × n` matrices (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1),
Eq. (4.5), p.33, `L_y = L_{S(y)}`; `L_S` as in Section 5.1, p.37). -/
noncomputable def Lmap {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, ∑ j, G i j • (normB A S i * normB A S j)

end MatrixLeeSidford


