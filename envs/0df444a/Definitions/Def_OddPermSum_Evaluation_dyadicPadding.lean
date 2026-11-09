-- Prove2me | Definitions.Def_OddPermSum_Evaluation_dyadicPadding
-- name    : OddPermSum_Evaluation_dyadicPadding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:34.742197+00:00
-- url     : https://prove2.me/theorems/8fc794ed-0714-421d-8daf-4e49a5d306ca
-- title:
--   Padding to the smallest positive dyadic order
-- statement:
--   Let $N=2^{\lceil\log_2 n\rceil}$ for $n\ge1$, with $N=1$ at $n=0$. The padded matrix is
--
--   $$\widetilde A=A\oplus I_{N-n}.$$
--
--   Its first $n$ rows and columns retain the original order. The implementation uses the natural-number ceiling logarithm and explicit block entries, so no matrix inverse or rank oracle is part of this construction. This connects arbitrary dimensions to the complete interval trees.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 7, padding preamble before Lemma 3.2

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- The smallest positive dyadic order at least n, including order one at n=0. -/
def paddingSize (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

/-- A ⊕ I in the original order; for n=0 this is the one-by-one identity. -/
def dyadicPadding {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (paddingSize n)) (Fin (paddingSize n)) R :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else if j.val < n then 0 else if i = j then 1 else 0

end OddPermSum.Evaluation


