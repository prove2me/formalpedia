-- Prove2me | Definitions.Def_DerivationHitting_Commutative_Supplement_MatrixData
-- name    : DerivationHitting_Commutative_Supplement_MatrixData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:32.861199+00:00
-- url     : https://prove2.me/theorems/26619691-e9d7-4ebc-8103-69ff44fe8704
-- title:
--   The exact §5 and Appendix A integration matrices
-- statement:
--   Let n,s be nonnegative integers. Reuse the published cutoff B=ns²+s. The rational §5 matrix for letter i=1,…,n, in the basis 1,t,…,t^{B−1}, has entries
--
--   $$\widetilde T_i(r,k)=\begin{cases}(-1)^{r-k-1}i^{r-k}/r&k<r<B,\\0&\text{otherwise.}\end{cases}$$
--
--   Its rational entries are specified by signed integer numerators and positive natural denominators, with zero represented by (0,1); the field-valued matrices use the canonical rational cast. Separately define N=(s−1)+binom(s,2)(n−1), using natural predecessors, and d=N+1. The appendix matrices in dimension d have entries
--
--   $$T'_i(r,k)=\begin{cases}i^{r-k}/r&0\le k<r\le N,\\0&\text{otherwise.}\end{cases}$$
--
--   Every active denominator r is positive. The first family corresponds to i/(1+it); the second to i/(1−it). These definitions retain exact cutoffs and do not identify the two kernels. With n=0 the tuple is empty. The appendix dimension is always positive, including s=0.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. p.21, proof of Theorem 5.12; p.29, equation (A.5).

import Definitions.Def_DerivationHitting_Commutative_Supplement_NCABPData
import Definitions.Def_DerivationHitting_Commutative_PolynomialData

namespace DerivationHitting.Commutative.Supplement

/-- Signed numerator and positive denominator; no gcd computation is needed. -/
def sectionEntryPair (i r k : ℕ) : ℤ × ℕ :=
  if k < r then ((-1 : ℤ) ^ (r - k - 1) * ((i + 1 : ℕ) : ℤ) ^ (r - k), r)
  else (0, 1)

def sectionRationalMatrices (n s : ℕ) (i : Fin n) :
    Matrix (Fin (cutoff n s)) (Fin (cutoff n s)) ℚ :=
  fun r k => let p := sectionEntryPair i.val r.val k.val
    (p.1 : ℚ) / (p.2 : ℚ)

noncomputable def sectionMatrices {F : Type*} [Field F] [CharZero F] (n s : ℕ)
    (i : Fin n) : Matrix (Fin (cutoff n s)) (Fin (cutoff n s)) F :=
  fun r k => (sectionRationalMatrices n s i r k : F)

/-- Natural predecessors extend the printed positive-parameter formula to zero parameters. -/
def appendixOrder (n s : ℕ) : ℕ := (s - 1) + Nat.choose s 2 * (n - 1)

def appendixDimension (n s : ℕ) : ℕ := appendixOrder n s + 1

/-- Equation (A.5), from i/(1−it), has no alternating sign. -/
noncomputable def appendixMatrices {F : Type*} [Field F] [CharZero F] (n s : ℕ)
    (i : Fin n) : Matrix (Fin (appendixDimension n s)) (Fin (appendixDimension n s)) F :=
  fun r k => if k.val < r.val then
    ((i.val + 1 : ℕ) : F) ^ (r.val - k.val) / (r.val : F) else 0

end DerivationHitting.Commutative.Supplement


