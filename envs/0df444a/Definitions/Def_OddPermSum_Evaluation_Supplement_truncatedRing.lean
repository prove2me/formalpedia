-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_truncatedRing
-- name    : OddPermSum_Evaluation_Supplement_truncatedRing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:08.226186+00:00
-- url     : https://prove2.me/theorems/aceee322-33be-47ed-950d-0e3dccaa68e7
-- title:
--   Truncated polynomial arithmetic and coefficient encodings
-- statement:
--   For a field $F$ and an integer $L\ge0$, put
--   $$R_L=F[z]/(z^{L+1}).$$
--   Coefficients are read from the remainder of any quotient representative modulo the monic polynomial $z^{L+1}$. Elements are encoded by coefficients $0,\ldots,L$, including trailing zeroes; matrices are encoded in row-major order. The matrix $A(0)$ consists of the constant coefficients.
--
--   This is the full truncated ring, with its nilpotents and unit convention; it is not replaced by a field or by pointwise polynomial evaluation.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 6 and 14, truncated arithmetic

import Definitions.Def_OddPermSum_Evaluation_matrixEncoding

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

/-- The quotient by z^(L+1), with all L+1 coefficients retained. -/
abbrev Trunc (F : Type*) [Field F] (L : ℕ) :=
  Polynomial F ⧸ Ideal.span ({Polynomial.X ^ (L+1)} : Set (Polynomial F))

/-- Reduce any representative modulo the monic truncation polynomial before taking coefficients. -/
noncomputable def truncCoeff {F : Type*} [Field F] {L : ℕ} (a : Trunc F L) (k : ℕ) : F :=
  ((Quotient.out a) %ₘ (Polynomial.X ^ (L+1))).coeff k

noncomputable def truncEncoding {F : Type*} [Field F] {L : ℕ} (a : Trunc F L) : List F :=
  List.ofFn (fun k : Fin (L+1) => truncCoeff a k.val)

noncomputable def truncMatrixEncoding {F : Type*} [Field F] {s L : ℕ}
    (A : Matrix (Fin s) (Fin s) (Trunc F L)) : List F :=
  (matrixEncoding A).flatMap truncEncoding

noncomputable def constantMatrix {F : Type*} [Field F] {s L : ℕ}
    (A : Matrix (Fin s) (Fin s) (Trunc F L)) : Matrix (Fin s) (Fin s) F :=
  fun i j => truncCoeff (A i j) 0

end OddPermSum.Evaluation.Supplement


