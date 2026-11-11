-- Prove2me | Definitions.Def_SchattenSketch_Main_Tensor
-- name    : SchattenSketch_Main_Tensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:38.440548+00:00
-- url     : https://prove2.me/theorems/19087088-1fe1-496a-8c25-97ed2fda52cb
-- title:
--   The tensor space $H^{\otimes m}$ over $H=\mathbb R^{n\times n}$, the two-sided rotation $(U\otimes V)^{\otimes m}$ and $P^{\otimes m}$
-- statement:
--   Let $H=\mathbb R^{n\times n}$, identified with $\mathbb R^n\otimes\mathbb R^n$ through $A\mapsto\sum_{i,j}A_{ij}\,e_i\otimes e_j$ (4.21a). An element $T$ of $H^{\otimes m}$ is a real array indexed by $m$ matrix positions $((a_1,b_1),\dots,(a_m,b_m))$; its **Frobenius norm** is $\|T\|^2=\sum T((a_s,b_s)_s)^2$.
--
--   The **two-sided rotation** applies $A\mapsto UAV^\top$ in every slot (4.21b)–(4.21c):
--   $$\bigl((U\otimes V)^{\otimes m}T\bigr)\bigl((a_s,b_s)_{s}\bigr)=\sum_{(i_s,j_s)_s}\ \prod_{s=1}^m U_{a_s i_s}V_{b_s j_s}\;T\bigl((i_s,j_s)_s\bigr).$$
--   For a linear operator $P$ on $H$, given as an $n^2\times n^2$ matrix, $P^{\otimes m}$ applies $P$ in every slot:
--   $(P^{\otimes m}T)((p_s)_s)=\sum_{(q_s)_s}\prod_s P_{p_s q_s}\,T((q_s)_s)$.
--
--   **Formalization Note.** `MatTensor n m` is `(Fin m → Fin n × Fin n) → ℝ`; `tensorNormSq`, `rotTensor U V` and `projTensor P` are the three displayed formulas, with $U,V$ arbitrary real $n\times n$ matrices.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 18, (4.21a)–(4.21c); p. 19, Lemma 4.6

import Mathlib

namespace SchattenSketch.Main

/-- The tensor space `H^{⊗m}` over `H = ℝ^{n×n}` (Yang, pp. 18–19): an order-`m` tensor is a real
array indexed by `m` matrix positions `((a₁, b₁), …, (a_m, b_m))`, slot `s` carrying a row index
`a_s` and a column index `b_s` (the identification (4.21a)). -/
abbrev MatTensor (n m : ℕ) : Type := (Fin m → Fin n × Fin n) → ℝ

/-- Squared Frobenius norm `‖T‖² = ∑ T(idx)²` of a tensor in `H^{⊗m}`. -/
def tensorNormSq {n m : ℕ} (T : MatTensor n m) : ℝ :=
  ∑ idx : Fin m → Fin n × Fin n, T idx ^ 2

/-- The two-sided rotation `(U ⊗ V)^{⊗m}` (4.21b)–(4.21c) (Yang, p. 18): the map `A ↦ U A Vᵀ`
applied in every one of the `m` slots,
`((U ⊗ V)^{⊗m} T)((a_s, b_s)_s) = ∑_{(i_s, j_s)_s} ∏_s U_{a_s i_s} V_{b_s j_s} · T((i_s, j_s)_s)`. -/
def rotTensor {n m : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ) (T : MatTensor n m) : MatTensor n m :=
  fun idx => ∑ jdx : Fin m → Fin n × Fin n,
    (∏ s : Fin m, U (idx s).1 (jdx s).1 * V (idx s).2 (jdx s).2) * T jdx

/-- `P^{⊗m}`: the `n² × n²` matrix `P` (a linear operator on `H = ℝ^{n×n}`) applied in every one of
the `m` slots (Yang, p. 19, Lemma 4.6). -/
def projTensor {n m : ℕ} (P : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (T : MatTensor n m) :
    MatTensor n m :=
  fun idx => ∑ jdx : Fin m → Fin n × Fin n, (∏ s : Fin m, P (idx s) (jdx s)) * T jdx

end SchattenSketch.Main


