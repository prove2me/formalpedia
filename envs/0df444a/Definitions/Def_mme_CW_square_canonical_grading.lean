-- Prove2me | Definitions.Def_mme_CW_square_canonical_grading
-- name    : mme_CW_square_canonical_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T20:20:28.991473+00:00
-- url     : https://prove2.me/theorems/56c375d5-62ed-44b9-b529-ca3708286e6d
-- title:
--   Canonical five-grading of the squared CW tensor
-- statement:
--   For the Coppersmith--Winograd tensor $T_q$, grade the outer coordinate by $0$, each of the $q$ middle coordinates by $1$, and the terminal coordinate by $2$.  In each mode of $T_q\otimes T_q$, grade a canonical basis pair by the sum of its two coordinate grades.  The five spans form an internal direct sum and hence define one canonical type grading with grades $0,1,2,3,4$.  This is the shared, source-faithful grading used by every scalar, rectangular, central, and coupled orbit certificate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, the fifteen constituents of the five-grading of the squared CW tensor.

import Definitions.Def_mme_CW_square_five_grade_certificate
import Mathlib.LinearAlgebra.TensorProduct.Basis

open TensorProduct DirectSum Module

namespace MME

universe u

/-- The span of basis vectors carrying one fixed grade. -/
def cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι → κ) (a : κ) : Submodule K V :=
  Submodule.span K (b '' {i | g i = a})

/-- A partition of a basis by grades is an internal direct sum. -/
theorem cwBasisGrade_isInternal
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι → κ) :
    DirectSum.IsInternal (cwBasisGrade b g) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro a
    simp_rw [cwBasisGrade]
    rw [← Submodule.span_iUnion₂]
    rw [← Set.image_iUnion₂]
    apply b.linearIndependent.disjoint_span_image
    rw [Set.disjoint_left]
    intro i hi hi'
    simp only [Set.mem_setOf_eq] at hi
    rcases Set.mem_iUnion.mp hi' with ⟨c, hi'⟩
    rcases Set.mem_iUnion.mp hi' with ⟨hc, hi'⟩
    exact hc (hi'.symm.trans hi)
  · apply top_unique
    rw [← b.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact le_iSup (cwBasisGrade b g) (g i) <|
      Submodule.subset_span ⟨i, rfl, rfl⟩

/-- Grade of a CW coordinate: outer, middle, and terminal coordinates have
grades `0`, `1`, and `2`. -/
def cwSquareCoordGrade (q : ℕ) (a : Fin (q + 2)) : Fin 3 :=
  if a.val = 0 then 0 else if a.val = q + 1 then 2 else 1

/-- Grade of a basis pair in the Kronecker square, obtained by adding the two
coordinate grades. -/
def cwSquarePairGrade (q : ℕ)
    (ab : Fin (q + 2) × Fin (q + 2)) : Fin 5 :=
  ⟨(cwSquareCoordGrade q ab.1).val +
    (cwSquareCoordGrade q ab.2).val, by omega⟩

/-- The canonical tensor-product basis in each mode of `T_q ⊗ T_q`. -/
noncomputable def cwSquareCanonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (Fin (q + 2) × Fin (q + 2)) K
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V s) := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  exact match s with
    | ⟨0, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))
    | ⟨1, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))
    | ⟨2, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))

/-- The source-faithful five-grading of `T_q ⊗ T_q`: each graded subspace is
the span of canonical basis pairs whose coordinate grades sum to that grade. -/
noncomputable def cwSquareCanonicalGrading
    (K : Type u) [Field K] (q : ℕ) :
    (TensorObj.kron (CWObj K q) (CWObj K q)).TypeGrading 5 where
  decomp s := cwBasisGrade (cwSquareCanonicalBasis K q s)
    (cwSquarePairGrade q)
  is_internal s := cwBasisGrade_isInternal
    (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q)

end MME


