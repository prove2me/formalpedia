-- Prove2me | Definitions.Def_BMPV1173_Verification_Supplement_RowSearch
-- name    : BMPV1173_Verification_Supplement_RowSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:51:57.621524+00:00
-- url     : https://prove2.me/theorems/193a947f-216b-4de0-ba89-9a90f8214f79
-- title:
--   Boolean Matrix Product Row Search and its all-ones restriction
-- statement:
--   For arbitrary Boolean $n\times n$ matrices $A,B$ and a Boolean target vector $v$, row search accepts exactly when
--
--   $$\exists i\in[n]\;\forall j\in[n],\quad (A\mathbin\bullet B)_{ij}=v_j.$$
--
--   The input index is a disjoint union selecting one of two matrix bits or a target-vector bit. A product adapter copies the two matrices into the published Boolean-product input; its unused third matrix is fixed to zero. The all-ones restriction fixes $v=1^n$ and removes target-vector coordinates from the unknown oracle. The resulting query complexities use the existing least worst-case count and success at least $2/3$. This separates the general target problem from its restriction without imposing any promise on either matrix.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Definition 5.1, printed p.34 = PDF p.34.

import Definitions.Def_BMPV1173_Verification_QueryComplexity

/-! Definition 5.1: two arbitrary Boolean matrices and a target vector.
The all-ones target restriction removes the vector from the unknown input. -/
namespace BMPV1173.Verification.Supplement

abbrev TwoMatrixIndex (n : ℕ) := Fin 2 × MatrixIndex n
abbrev RowSearchIndex (n : ℕ) := TwoMatrixIndex n ⊕ Fin n

/-- The first two matrices are copied; the third matrix is unused by the product. -/
def productInput {n : ℕ} (x : TwoMatrixIndex n → Bool) : VerificationInput n :=
  fun q => if q.1 = 0 then x (0, q.2)
    else if q.1 = 1 then x (1, q.2) else false

noncomputable def bmprs {n : ℕ} (x : RowSearchIndex n → Bool) : Bool := by
  classical
  exact decide (∃ i : Fin n, ∀ j : Fin n,
    booleanProduct (productInput (fun q => x (Sum.inl q))) i j = x (Sum.inr j))

def allOnesTarget {n : ℕ} (x : TwoMatrixIndex n → Bool) : RowSearchIndex n → Bool :=
  Sum.elim x (fun _ => true)

noncomputable def bmprsOne {n : ℕ} (x : TwoMatrixIndex n → Bool) : Bool :=
  bmprs (allOnesTarget x)

noncomputable def qBMPRS (n : ℕ) : ENat := queryComplexity Set.univ (@bmprs n)
noncomputable def qBMPRSOne (n : ℕ) : ENat := queryComplexity Set.univ (@bmprsOne n)

end BMPV1173.Verification.Supplement


