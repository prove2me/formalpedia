-- Prove2me | Definitions.Def_mme_dwz_cw_square_fine_split_grading
-- name    : mme_dwz_cw_square_fine_split_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T04:56:17.745435+00:00
-- url     : https://prove2.me/theorems/0407f7b9-bdc3-43aa-8821-3bba7fd0aa7e
-- title:
--   Fine two-half grading of the Coppersmith–Winograd square
-- statement:
--   For the square of the Coppersmith–Winograd tensor, retain the two level-one grades separately. Each mode coordinate is labelled by a pair $(a,b)$ with $a,b$ in $\{0,1,2\}$, instead of only by the coarse sum $a+b$. Thus the grading has nine classes and refines the usual five-class grading. The interface also provides the two projections from a fine label and the inverse pairing identity. This is the source-level grading used in the additional zeroing steps of asymmetric hashing, where the split of each coarse grade between the two tensor factors must remain visible. **Formalization Note** The grading is the product of the canonical three-gradings of the two CW factors.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1 Additional Zeroing-Out Step 1 and Claim 6.2 (PDF pp. 51–52 / printed pp. 50–51), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.Tactic

open DirectSum Module

namespace MME.DWZStep1Support

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

/-- The coordinate basis in one mode of the Coppersmith--Winograd tensor. -/
noncomputable def cwThreeCanonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (Fin (q + 2)) K ((CWObj K q).V s) := by
  exact match s with
    | ⟨0, _⟩ => Pi.basisFun K (Fin (q + 2))
    | ⟨1, _⟩ => Pi.basisFun K (Fin (q + 2))
    | ⟨2, _⟩ => Pi.basisFun K (Fin (q + 2))

/-- The source-faithful three-grading of `CW_q`: outer, middle, and terminal
coordinates have grades `0`, `1`, and `2`. -/
noncomputable def cwThreeCanonicalGrading
    (K : Type u) [Field K] (q : ℕ) :
    (CWObj K q).TypeGrading 3 where
  decomp s := cwBasisGrade (cwThreeCanonicalBasis K q s)
    (cwSquareCoordGrade q)
  is_internal s := cwBasisGrade_isInternal
    (cwThreeCanonicalBasis K q s) (cwSquareCoordGrade q)

/-- The fine nine-grading of `CW_q tensor CW_q`, retaining the two level-one
grades separately instead of only their sum. -/
noncomputable def cwSquareFineSplitGrading
    (K : Type u) [Field K] (q : ℕ) :
    (TensorObj.kron (CWObj K q) (CWObj K q)).TypeGrading (3 * 3) :=
  TensorObj.TypeGrading.kronGrading
    (cwThreeCanonicalGrading K q) (cwThreeCanonicalGrading K q)

/-- Encode the two level-one grades as the label of the fine nine-grading. -/
def fineSplitGrade (a b : Fin 3) : Fin (3 * 3) :=
  finProdFinEquiv (a, b)

/-- Recover the left level-one grade from a fine grade. -/
def fineSplitLeft (a : Fin (3 * 3)) : Fin 3 :=
  (finProdFinEquiv.symm a).1

/-- Recover the right level-one grade from a fine grade. -/
def fineSplitRight (a : Fin (3 * 3)) : Fin 3 :=
  (finProdFinEquiv.symm a).2

@[simp] theorem fineSplitLeft_encode (a b : Fin 3) :
    fineSplitLeft (fineSplitGrade a b) = a := by
  simp [fineSplitLeft, fineSplitGrade]

@[simp] theorem fineSplitRight_encode (a b : Fin 3) :
    fineSplitRight (fineSplitGrade a b) = b := by
  simp [fineSplitRight, fineSplitGrade]

theorem fineSplitGrade_eta (a : Fin (3 * 3)) :
    fineSplitGrade (fineSplitLeft a) (fineSplitRight a) = a := by
  simp [fineSplitGrade, fineSplitLeft, fineSplitRight]

end MME.DWZStep1Support


