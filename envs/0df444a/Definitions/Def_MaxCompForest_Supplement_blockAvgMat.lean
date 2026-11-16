-- Prove2me | Definitions.Def_MaxCompForest_Supplement_blockAvgMat
-- name    : MaxCompForest_Supplement_blockAvgMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:08:31.506517+00:00
-- url     : https://prove2.me/theorems/9739802c-5e22-40e5-ba4d-87d407037fd0
-- title:
--   Degree-weighted block averaging $P_Q$
-- statement:
--   Let $Q$ be a partition of the vertex set $V$ into nonempty blocks and $d_v>0$ masses. With $R_Q$ the $V\times Q$ block-indicator matrix and $D=\mathrm{diag}(d_v)$, the **degree-weighted block-averaging operator** is
--
--   $$P_Q=R_Q\,(R_Q^{\top}DR_Q)^{-1}R_Q^{\top}D,\qquad (P_Qf)_v=\frac{\sum_{u\in B(v)} d_u f_u}{\sum_{u\in B(v)} d_u},$$
--
--   where $B(v)$ is the block containing $v$. It replaces a signal by its degree-weighted block means.
--
--   **Formalization Note** A partition is a Mathlib `Finpartition` of the whole vertex set; the matrix is written entrywise, $P_Q(v,u)=d_u/d(B(v))$ for $u\in B(v)$ and $0$ otherwise. The masses are degrees of a connected graph with at least two vertices, so every block mass is positive.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (5.1), p.28 (PDF p.30)

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Degree-weighted block averaging** `P_Q = R_Q (R_Qᵀ D R_Q)⁻¹ R_Qᵀ D` of a partition `Q` of the vertex set:
`(P_Q f)_v = (∑_{u ∈ B(v)} d_u f_u) / (∑_{u ∈ B(v)} d_u)`, where `B(v)` is the block of `v`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (5.1), p.28.

**Formalization Note.** A partition is a Mathlib `Finpartition` of `Finset.univ` (blocks are nonempty and
disjoint and cover `V`); `Q.part v` is the block of `v`. The matrix is written entrywise:
`P_Q(v,u) = d_u / d(B(v))` if `u ∈ B(v)` and `0` otherwise, which is the product `R_Q (R_Qᵀ D R_Q)⁻¹ R_Qᵀ D`.
Masses are the degrees of a connected graph on at least two vertices, so every block mass is positive. -/
noncomputable def blockAvgMat (W : V → ℝ) (Q : Finpartition (Finset.univ : Finset V)) : Matrix V V ℝ :=
  fun v u => if u ∈ Q.part v then W u / ∑ w ∈ Q.part v, W w else 0

end MaxCompForest.Supplement


