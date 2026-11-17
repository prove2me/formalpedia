-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_gradMatG
-- name    : MatrixLeeSidford_Supplement_gradMatG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:13:12.153205+00:00
-- url     : https://prove2.me/theorems/e76e5dfe-7724-4360-9d51-a3b0cc5a6b1c
-- title:
--   Gradient matrix $M=\frac12(L_y(G)^s+\sum_aV_aL_y(G)^{s-1}V_a)$ at a query state
-- statement:
--   Let $y$ be feasible, $B_i=S(y)^{-1/2}A_iS(y)^{-1/2}$, and let $G\succ0$ have Cholesky factor $L$. With $V_a:=\sum_iL_{ia}B_i$ for $a\in[m]$, the **gradient matrix** at the query state $(y,G)$ is
--   $$
--   M:=\frac12\Big(L_y(G)^s+\sum_aV_a\,L_y(G)^{s-1}\,V_a\Big).
--   $$
--   Since $\sum_aV_aXV_a=\sum_{i,j}G_{ij}B_iXB_j$, $M$ depends on $G$ only; at $G=G_*(y)$ it is the matrix $M_y$ of Definition 5.5.
--
--   **Formalization Note** $V_a$ is built from the Cholesky factor, as printed; powers are natural-number matrix powers.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 8.1, p.53

import Mathlib
import Definitions.Def_MatrixLeeSidford_Lmap
import Definitions.Def_MatrixLeeSidford_slack
import Definitions.Def_MatrixLeeSidford_Supplement_cholFactor

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **gradient matrix** at a query state `(y, G)`,
`M := ½ (L_y(G)^s + ∑_a V_a L_y(G)^{s−1} V_a)` with `V_a := ∑_i L_{ia} B_i` and `L` the Cholesky factor of
`G` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 8.1, p.53).

**Formalization Note** `B_i = normB A (S(y)) i`, `L_y = Lmap A (S(y))`, `L = cholFactor G`; powers are
natural-number matrix powers. -/
noncomputable def gradMatG {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (y : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let V : Fin m → Matrix (Fin n) (Fin n) ℝ :=
    fun a => ∑ i, cholFactor G i a • normB A (slack A C y) i
  (1 / 2 : ℝ) • ((Lmap A (slack A C y) G) ^ s +
    ∑ a, V a * (Lmap A (slack A C y) G) ^ (s - 1) * V a)

end MatrixLeeSidford.Supplement


