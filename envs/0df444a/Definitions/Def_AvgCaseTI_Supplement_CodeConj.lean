-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_CodeConj
-- name    : AvgCaseTI_Supplement_CodeConj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:26:40.883203+00:00
-- url     : https://prove2.me/theorems/e6e10c25-a5a0-4753-b075-b7549ea23029
-- title:
--   Matrix code conjugacy of $n\times n\times n$ arrays in $U\otimes U^*\otimes V$
-- statement:
--   Let $\mathbb F$ be a field and $A=(a_{i,j,k}),B=(b_{i,j,k})$ two $n\times n\times n$ arrays over $\mathbb F$, viewed as elements of $U\otimes U^*\otimes V$ with $U\cong V\cong\mathbb F^n$. Their **frontal slices** are the $n\times n$ matrices $A_k(i,j)=a_{i,j,k}$, $k\in[n]$ (the index $k$ runs over $V$).
--
--   The arrays are **conjugate matrix codes** when there are invertible matrices $S,T\in\mathrm{GL}(n,\mathbb F)$ with
--   $$
--   B_k=\sum_{\ell=1}^{n} t_{k\ell}\,S A_\ell S^{-1}\qquad\text{for every }k\in[n].
--   $$
--   This is the natural action of $\mathrm{GL}(U)\times\mathrm{GL}(V)$ on $U\otimes U^*\otimes V$: $S$ acts on $U$, its inverse transpose on $U^*$, and $T$ on $V$. When the slices are linearly independent it says that $S$ conjugates the code $\mathcal A=\langle A_1,\dots,A_n\rangle$ onto $\mathcal B$, as in Eq. (10) of the paper.
--
--   **Formalization Note** The relation is stated on the arrays themselves, so it is also defined for arrays with linearly dependent slices.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.2, p.5 (PDF p.7); §3.2, Eq. (10), p.22 (PDF p.24); §2.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_AvgCaseTI_Tensor3

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

variable {K : Type*} [Field K] {n : ℕ}

/-- The frontal slice `A_k(i, j) = a_{i,j,k}` of a 3-way array (§2.3, p.15, PDF p.17): the `k`-th
matrix of the matrix code in `U ⊗ U* ⊗ V`, `k` the `V`-index. -/
def frontal (A : Tensor3 K n) (k : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => A i j k

/-- **Matrix code conjugacy of 3-way arrays in `U ⊗ U* ⊗ V`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 1.2, p.5 (PDF p.7): "given A, B ∈ U ⊗ U∗ ⊗ V, decide whether they are isomorphic
under the natural action of GL(U) × GL(V)", and §3.2, Eq. (10), p.22 (PDF p.24): "They are conjugate
if there exist S ∈ GL(n, q) and T = (t_ij) ∈ GL(n, q) such that B_i = Σ_j t_ij S A_j S^{−1}".

`CodeConj A B` holds when there are invertible `S, T` with `B_k = Σ_l T_{k l} · S A_l S^{−1}` for every
`k`, where `A_k, B_k` are the frontal slices.

**Formalization Note.** This is the action `(S, T) · A = (S ⊗ S^{−t} ⊗ T) · A` of `GL(U) × GL(V)` on
`U ⊗ U* ⊗ V` written on slices; it is the relation between the arrays themselves, so it also covers
arrays whose slices are linearly dependent. -/
def CodeConj (A B : Tensor3 K n) : Prop :=
  ∃ S T : GL (Fin n) K, ∀ k : Fin n,
    frontal B k = ∑ l : Fin n, (T : Matrix (Fin n) (Fin n) K) k l •
      ((S : Matrix (Fin n) (Fin n) K) * frontal A l * ((S⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))

end AvgCaseTI.Supplement


