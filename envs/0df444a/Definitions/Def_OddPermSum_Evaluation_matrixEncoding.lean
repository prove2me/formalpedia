-- Prove2me | Definitions.Def_OddPermSum_Evaluation_matrixEncoding
-- name    : OddPermSum_Evaluation_matrixEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:44.811199+00:00
-- url     : https://prove2.me/theorems/73f52fc8-6576-4c6c-acaa-7e59ac8dad9c
-- title:
--   Row-major matrix input and output
-- statement:
--   Entries of a square matrix are serialized in increasing row order, then increasing column order:
--
--   $$\operatorname{enc}(A)=[A_{0,0},\ldots,A_{0,n-1},A_{1,0},\ldots,A_{n-1,n-1}].$$
--
--   The empty matrix has empty encoding. A multiplication routine receives the encodings of its two matrices concatenated; the simultaneous evaluator outputs the scalar $\Phi(A)$ followed by the encoding of the entire matrix $G(A)$. This is an interface convention and supplies no computational primitive.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Theorem 1.1; p. 5, index conventions (serialization encoding)

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Canonical row-major list. In particular the 0 by 0 matrix is the empty list. -/
def matrixEncoding {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : List R :=
  (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => A i j).flatten

end OddPermSum.Evaluation


