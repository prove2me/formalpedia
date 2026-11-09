-- Prove2me | Definitions.Def_OddPermSum_Evaluation_intervalSplits
-- name    : OddPermSum_Evaluation_intervalSplits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:24.62013+00:00
-- url     : https://prove2.me/theorems/04eadb0c-f2d3-481e-bca3-df1f6addc4d4
-- title:
--   Complete ordered binary interval tree and trace contributions
-- statement:
--   On $\mathrm{Fin}(2^h)$, every depth $a<h$ has $2^a$ internal nodes. At node $b$, its left and right children have equal length $s=2^{h-a-1}$ and zero-based intervals $[2bs,(2b+1)s)$ and $[(2b+1)s,(2b+2)s)$. The collection of these child pairs is the source's row or column split collection. At $h=0$ it is empty.
--
--   For row children $(I,J)$ and column children $(L,K)$ the contribution is
--
--   $$\operatorname{tr}\big(A[I,K]B[K,J]A[J,L]B[L,I]\big).$$
--
--   Submatrices are indexed by the corresponding finite subsets, so these are genuine rectangular matrix products followed by a square trace.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 7, binary interval tree preamble and Eq. (3.7)

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Equal left/right children at every internal node of the complete ordered dyadic tree.
Sets use zero-based indices, so the root interval is [0, 2^h). -/
def intervalSplits (h : ℕ) : Finset (Finset (Fin (2^h)) × Finset (Fin (2^h))) :=
  (Finset.range h).biUnion fun a =>
    (Finset.range (2^a)).image fun b =>
      let s := 2^(h-a-1)
      (Finset.univ.filter (fun i => 2*b*s ≤ i.val ∧ i.val < (2*b+1)*s),
       Finset.univ.filter (fun i => (2*b+1)*s ≤ i.val ∧ i.val < (2*b+2)*s))

/-- Trace of the four rectangular submatrix products, on their inherited index subtypes. -/
noncomputable def splitTrace {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (I J L K : Finset (Fin n)) : R :=
  Matrix.trace
    ((A.submatrix (fun i : I => i.val) (fun k : K => k.val)) *
     (B.submatrix (fun k : K => k.val) (fun j : J => j.val)) *
     (A.submatrix (fun j : J => j.val) (fun l : L => l.val)) *
     (B.submatrix (fun l : L => l.val) (fun i : I => i.val)))

end OddPermSum.Evaluation


