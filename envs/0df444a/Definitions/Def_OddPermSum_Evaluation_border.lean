-- Prove2me | Definitions.Def_OddPermSum_Evaluation_border
-- name    : OddPermSum_Evaluation_border
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:49.367791+00:00
-- url     : https://prove2.me/theorems/84049e3c-f001-44cf-932b-bea6ea5f4113
-- title:
--   Fixed rank-minor border
-- statement:
--   For a field matrix $A$ of rank $r$ and corank $k$, select row and column sets $I,J$ of size $r$ with unit minor determinant, and list their complements increasingly as $i_a,j_a$, $a\in\mathrm{Fin}(k)$. The data records this rank minor and these ordered complement lists. With $U=(e_{i_a})_a$ and $V=(e_{j_a})_a$, define, for arbitrary $X,t$,
--
--   $$M_X(t)=\begin{pmatrix}X&U\\ V^{\mathsf T}&\operatorname{diag}(t)\end{pmatrix}.$$
--
--   The entry formula works over any commutative coefficient ring, including the polynomial ring in the entries of $X$. The border stays fixed when $X$ varies. No independent row or column permutation is applied to the matrix on which $\Phi$ is evaluated.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), pp. 8–9, Eq. (3.9) and Lemma 3.5 preamble

import Definitions.Def_OddPermSum_Evaluation_orderedMinor

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Fixed standard-basis border, in the original order. The complement maps are
increasing enumerations supplied by the selected rank minor, never functions of X. -/
def border {R : Type*} [CommRing R] {n k : ℕ}
    (rows cols : Fin k → Fin n) (X : Matrix (Fin n) (Fin n) R) (t : Fin k → R) :
    Matrix (Fin (n+k)) (Fin (n+k)) R :=
  fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then X ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else if (⟨i.val, hi⟩ : Fin n) = rows ⟨j.val-n, by omega⟩ then 1 else 0
    else if hj : j.val < n then
      if (⟨j.val, hj⟩ : Fin n) = cols ⟨i.val-n, by omega⟩ then 1 else 0
    else if i.val-n = j.val-n then t ⟨i.val-n, by omega⟩ else 0

/-- The border data of (3.9): a full-rank ordered minor and increasing complement lists. -/
structure RankBorder {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (k : ℕ) where
  I : Finset (Fin n)
  J : Finset (Fin n)
  corank : Matrix.rank A + k = n
  rowCard : I.card = Matrix.rank A
  colCard : J.card = Matrix.rank A
  minorUnit : IsUnit (orderedMinor A I J rowCard colCard)
  rows : Fin k ↪o Fin n
  cols : Fin k ↪o Fin n
  rowRange : Set.range rows = {i | i ∉ I}
  colRange : Set.range cols = {j | j ∉ J}

end OddPermSum.Evaluation


