-- Prove2me | Definitions.Def_CSL_Circuit_Framework_UniformFactorization
-- name    : CSL_Circuit_Framework_UniformFactorization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:12:09.93188+00:00
-- url     : https://prove2.me/theorems/0f1e4999-de52-4ed6-ae7a-b5a06329d867
-- title:
--   Coded sorting library: Circuit / Framework / UniformFactorization
-- statement:
--   Module `CodedSorting.Circuit.Framework.UniformFactorization` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.UniformFactorization

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_MatrixFactorization

namespace CSL.MatrixFactorization

variable {I : Type*} [Fintype I] [DecidableEq I]

section UniformFactorizations

variable [LinearOrder I]

/-- Witness data for the proved rational factorization. -/
structure LowerFactorization (A : Matrix I I ℚ) where
  left : Matrix I I ℚ
  pivot : Matrix I I ℚ
  right : Matrix I I ℚ
  left_lower : LowerTriangular left
  right_lower : LowerTriangular right
  left_unit : IsUnit left
  right_unit : IsUnit right
  pivot_sparse : PartialMonomial pivot
  pivot_zero_one : ∀ i j, pivot i j = 0 ∨ pivot i j = 1
  equation : A = left * pivot * right
  rank_eq : pivot.rank = A.rank

noncomputable def chooseLowerFactorization (A : Matrix I I ℚ) : LowerFactorization A :=
  Classical.choice (show Nonempty (LowerFactorization A) from by
    obtain ⟨L, P, R, hL, hR, huL, huR, hP, h01, heq, hrank⟩ :=
      exists_lower_partialPermutation_factorization A
    exact ⟨{
      left := L
      pivot := P
      right := R
      left_lower := hL
      right_lower := hR
      left_unit := huL
      right_unit := huR
      pivot_sparse := hP
      pivot_zero_one := h01
      equation := heq
      rank_eq := hrank }⟩)

variable {K : Type*} [Fintype K] (A : K → Matrix I I ℚ)

/-- The finite data to specialize jointly: A, E1, P, E2, E1 inverse, E2 inverse. -/
noncomputable def expandedFamily (D : ∀ k, LowerFactorization (A k)) :
    K × Fin 6 → Matrix I I ℚ := fun x =>
  if x.2 = 0 then A x.1
  else if x.2 = 1 then (D x.1).left
  else if x.2 = 2 then (D x.1).pivot
  else if x.2 = 3 then (D x.1).right
  else if x.2 = 4 then (D x.1).left⁻¹
  else (D x.1).right⁻¹

/-- One explicitly constructed common localization and prime for a whole finite family. -/
structure UniformLowerFactorization where
  data : ∀ k, LowerFactorization (A k)
  specialization : SpecializedFamily (expandedFamily A data)

noncomputable def uniformLowerFactorization : UniformLowerFactorization A :=
  let D := fun k => chooseLowerFactorization (A k)
  ⟨D, specializeFamily (expandedFamily A D)⟩

namespace UniformLowerFactorization

variable {A} (U : UniformLowerFactorization A)

noncomputable def matrix (f : ℕ) (k : K) (slot : Fin 6) :
    Matrix I I (ZMod (U.specialization.prime ^ f)) :=
  U.specialization.matrix f (k, slot)

theorem factorization (k : K) (f : ℕ) :
    U.matrix f k 0 = U.matrix f k 1 * U.matrix f k 2 * U.matrix f k 3 := by
  apply U.specialization.preserves_factorization (k, 0) (k, 1) (k, 2) (k, 3)
  simpa [expandedFamily] using (U.data k).equation

theorem left_inverse (k : K) (f : ℕ) :
    U.matrix f k 1 * U.matrix f k 4 = 1 ∧
    U.matrix f k 4 * U.matrix f k 1 = 1 := by
  apply U.specialization.preserves_two_sided_inverse (k, 1) (k, 4)
  · simpa [expandedFamily] using Matrix.mul_nonsing_inv (U.data k).left
      ((Matrix.isUnit_iff_isUnit_det _).mp (U.data k).left_unit)
  · simpa [expandedFamily] using Matrix.nonsing_inv_mul (U.data k).left
      ((Matrix.isUnit_iff_isUnit_det _).mp (U.data k).left_unit)

theorem right_inverse (k : K) (f : ℕ) :
    U.matrix f k 3 * U.matrix f k 5 = 1 ∧
    U.matrix f k 5 * U.matrix f k 3 = 1 := by
  apply U.specialization.preserves_two_sided_inverse (k, 3) (k, 5)
  · simpa [expandedFamily] using Matrix.mul_nonsing_inv (U.data k).right
      ((Matrix.isUnit_iff_isUnit_det _).mp (U.data k).right_unit)
  · simpa [expandedFamily] using Matrix.nonsing_inv_mul (U.data k).right
      ((Matrix.isUnit_iff_isUnit_det _).mp (U.data k).right_unit)

theorem left_lower (k : K) (f : ℕ) :
    ∀ i j, i < j → U.matrix f k 1 i j = 0 := by
  apply U.specialization.preserves_lower_triangular (k, 1)
  first
  | exact (U.data k).left_lower
  | (have h_sx := (U.data k).left_lower; simp [expandedFamily] at h_sx ⊢; exact h_sx)
  | (have h_sx := (U.data k).left_lower; simp [expandedFamily] at h_sx; exact h_sx)
  | (simp [expandedFamily]; exact (U.data k).left_lower)

theorem right_lower (k : K) (f : ℕ) :
    ∀ i j, i < j → U.matrix f k 3 i j = 0 := by
  apply U.specialization.preserves_lower_triangular (k, 3)
  first
  | exact (U.data k).right_lower
  | (have h_sx := (U.data k).right_lower; simp [expandedFamily] at h_sx ⊢; exact h_sx)
  | (have h_sx := (U.data k).right_lower; simp [expandedFamily] at h_sx; exact h_sx)
  | (simp [expandedFamily]; exact (U.data k).right_lower)

theorem left_isUnit (k : K) (f : ℕ) : IsUnit (U.matrix f k 1) :=
  isUnit_iff_exists.mpr ⟨U.matrix f k 4, (U.left_inverse k f).1, (U.left_inverse k f).2⟩

theorem right_isUnit (k : K) (f : ℕ) : IsUnit (U.matrix f k 3) :=
  isUnit_iff_exists.mpr ⟨U.matrix f k 5, (U.right_inverse k f).1, (U.right_inverse k f).2⟩

/-- The middle step uses exactly rank_Q(A) primitive coordinate shears for every q^f. -/
theorem sparse_step (k : K) (f : ℕ) {Value : Type*}
    (stream : (I → ZMod (U.specialization.prime ^ f)) ×
      (I → ZMod (U.specialization.prime ^ f)) → Value) :
    (unitShears (U.data k).pivot (ZMod (U.specialization.prime ^ f))).length =
      (A k).rank ∧
    CSL.Address.applyShears
      ((unitShears (U.data k).pivot (ZMod (U.specialization.prime ^ f))).map Matrix.mulVec)
      stream = CSL.Address.matrixPhi (U.matrix f k 2) stream := by
  have h := U.specialization.unitShears_correct (k, 2)
    (by simpa [expandedFamily] using (U.data k).pivot_sparse)
    (by simpa [expandedFamily] using (U.data k).pivot_zero_one) f stream
  simpa [expandedFamily, (U.data k).rank_eq, matrix] using h

/-- Coordinate changes around the sparse step realize h += A*d and restore d.
This is a concrete equality over every prime-power coefficient ring. -/
theorem address_update (k : K) (f : ℕ)
    (h d : I → ZMod (U.specialization.prime ^ f)) :
    ((U.matrix f k 1).mulVec ((U.matrix f k 4).mulVec h +
      (U.matrix f k 2).mulVec ((U.matrix f k 3).mulVec d)),
      (U.matrix f k 5).mulVec ((U.matrix f k 3).mulVec d)) =
    (h + (U.matrix f k 0).mulVec d, d) := by
  rw [Matrix.mulVec_add]
  simp only [Matrix.mulVec_mulVec, (U.left_inverse k f).1,
    (U.right_inverse k f).2, Matrix.one_mulVec]
  rw [← Matrix.mul_assoc, ← U.factorization k f]

end UniformLowerFactorization

end UniformFactorizations

end CSL.MatrixFactorization


