-- Prove2me | Definitions.Def_CSL_Circuit_Local_TriangularConjugacy
-- name    : CSL_Circuit_Local_TriangularConjugacy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:10:09.167862+00:00
-- url     : https://prove2.me/theorems/03d57788-b7cb-4518-ba98-7d6ca989e7f6
-- title:
--   Coded sorting library: Circuit / Local / TriangularConjugacy
-- statement:
--   Module `CodedSorting.Circuit.Local.TriangularConjugacy` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A rank-one reflection is a triangular conjugate of one transposition
--
--   For a nonzero rational vector `w`, choose its first and last nonzero indices
--   `i < j`.  The explicitly constructed matrix `factor w i j` is lower triangular
--   with nonzero diagonal.  The reflection in `w` exchanges its `i` and `j` columns
--   and fixes every other column.  Thus it is `factor * swap * factor⁻¹`.
--
--   For a partial field swap, `w = (u,-u)`: its first index is in H and its last
--   index is in D.  Exactly one ordinary short-field exchange is needed.
--
--   This file concerns the rational matrix identity, not a disk program, an
--   external-memory bound, or the final sorting theorem.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.TriangularConjugacy

import Definitions.Def_CSL_Compat
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Sum.Order
import Mathlib.Data.Finset.Max

/-!
# A rank-one reflection is a triangular conjugate of one transposition

For a nonzero rational vector `w`, choose its first and last nonzero indices
`i < j`.  The explicitly constructed matrix `factor w i j` is lower triangular
with nonzero diagonal.  The reflection in `w` exchanges its `i` and `j` columns
and fixes every other column.  Thus it is `factor * swap * factor⁻¹`.

For a partial field swap, `w = (u,-u)`: its first index is in H and its last
index is in D.  Exactly one ordinary short-field exchange is needed.

This file concerns the rational matrix identity, not a disk program, an
external-memory bound, or the final sorting theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CSL.Construction.TriangularConjugacy

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The coordinate basis vector, with row-first equality for simple rewriting. -/
def basis (j : I) : I → ℚ := fun r => if r = j then 1 else 0

omit [Fintype I] in
@[simp] theorem basis_self (j : I) : basis j j = 1 := by simp [basis]

omit [Fintype I] in
@[simp] theorem basis_of_ne (j r : I) (h : r ≠ j) : basis j r = 0 := by
  simp [basis, h]

@[simp] theorem dot_basis (w : I → ℚ) (j : I) : w ⬝ᵥ basis j = w j := by
  simp [dotProduct, basis, mul_ite]

/-- Squared Euclidean length over the rationals. -/
def normSq (w : I → ℚ) : ℚ := w ⬝ᵥ w

/-- Reflection across the orthogonal complement of `w`. -/
def reflection (w : I → ℚ) : Matrix I I ℚ :=
  1 - (2 / normSq w) • Matrix.vecMulVec w w

/-- The scalar attached to the last selected column. -/
def alpha (w : I → ℚ) (j : I) : ℚ := -normSq w / (2 * w j)

/-- The columns of the explicit triangular factor.  Outside the support of
`w`, the final branch is just the corresponding standard basis column. -/
def factorColumn (w : I → ℚ) (i j c : I) : I → ℚ :=
  if c = i then w + alpha w j • basis j
  else if c = j then alpha w j • basis j
  else basis c - (w c / w j) • basis j

def factor (w : I → ℚ) (i j : I) : Matrix I I ℚ :=
  fun r c => factorColumn w i j c r

/-- Right multiplication by this matrix exchanges columns `i` and `j`. -/
def swapMatrix (i j : I) : Matrix I I ℚ :=
  fun r c => (1 : Matrix I I ℚ) r (Equiv.swap i j c)

theorem mul_swapMatrix (A : Matrix I I ℚ) (i j r c : I) :
    (A * swapMatrix i j) r c = A r (Equiv.swap i j c) := by
  simp [swapMatrix, Matrix.mul_apply, Matrix.one_apply, mul_ite]

theorem reflection_mulVec (w x : I → ℚ) :
    reflection w *ᵥ x = x - ((2 / normSq w) * (w ⬝ᵥ x)) • w := by
  rw [reflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  ext r
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    Matrix.vecMulVec_apply, dotProduct]
  have hsum : (∑ k : I, (w r * w k) * x k) = w r * ∑ k : I, w k * x k := by
    simp only [mul_assoc, Finset.mul_sum]
  rw [hsum]
  ring

theorem reflection_on_direction (w : I → ℚ) (hn : normSq w ≠ 0) :
    reflection w *ᵥ w = -w := by
  rw [reflection_mulVec]
  have hc : (2 / normSq w) * (w ⬝ᵥ w) = 2 := by
    change (2 / normSq w) * normSq w = 2
    exact div_mul_cancel₀ _ hn
  rw [hc]
  ext r
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem reflection_on_basis (w : I → ℚ) (j : I) :
    reflection w *ᵥ basis j = basis j - ((2 / normSq w) * w j) • w := by
  simp only [reflection_mulVec, dot_basis]

theorem reflection_first_column (w : I → ℚ) (j : I)
    (hn : normSq w ≠ 0) (hj : w j ≠ 0) :
    reflection w *ᵥ (w + alpha w j • basis j) = alpha w j • basis j := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, reflection_on_direction w hn,
    reflection_on_basis]
  ext r
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  try dsimp [alpha]
  field_simp [hn, hj]
  ring

theorem reflection_last_column (w : I → ℚ) (j : I)
    (hn : normSq w ≠ 0) (hj : w j ≠ 0) :
    reflection w *ᵥ (alpha w j • basis j) = w + alpha w j • basis j := by
  rw [Matrix.mulVec_smul, reflection_on_basis]
  ext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  try dsimp [alpha]
  field_simp [hn, hj]
  ring

theorem reflection_other_column (w : I → ℚ) (j c : I) (hj : w j ≠ 0) :
    reflection w *ᵥ (basis c - (w c / w j) • basis j) =
      basis c - (w c / w j) • basis j := by
  have hz : w ⬝ᵥ (basis c - (w c / w j) • basis j) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dot_basis, dot_basis]
    simp only [smul_eq_mul, div_mul_cancel₀ _ hj, sub_self]
  rw [reflection_mulVec, hz, mul_zero, zero_smul, sub_zero]

/-- The main finite-dimensional matrix identity.  No ordering or support
conditions are needed for this identity itself, only `i ≠ j`. -/
theorem reflection_mul_factor (w : I → ℚ) (i j : I) (hij : i ≠ j)
    (hn : normSq w ≠ 0) (hj : w j ≠ 0) :
    reflection w * factor w i j = factor w i j * swapMatrix i j := by
  ext r c
  rw [mul_swapMatrix]
  change (reflection w *ᵥ factorColumn w i j c) r =
    factorColumn w i j (Equiv.swap i j c) r
  by_cases hci : c = i
  · subst c
    simp only [Equiv.swap_apply_left, factorColumn, if_pos rfl, if_neg hij.symm]
    exact congrFun (reflection_first_column w j hn hj) r
  by_cases hcj : c = j
  · subst c
    simp only [Equiv.swap_apply_right, factorColumn, if_pos rfl, if_neg hij.symm]
    exact congrFun (reflection_last_column w j hn hj) r
  · rw [Equiv.swap_apply_of_ne_of_ne hci hcj]
    simp only [factorColumn, if_neg hci, if_neg hcj]
    exact congrFun (reflection_other_column w j c hj) r

/-- Row-first convention for ordinary lower triangularity. -/
def LowerTriangular (A : Matrix I I ℚ) : Prop :=
  ∀ r c, r < c → A r c = 0

theorem factor_lower (w : I → ℚ) (i j : I) (hij : i < j)
    (hbefore : ∀ r, r < i → w r = 0)
    (hafter : ∀ r, j < r → w r = 0) :
    LowerTriangular (factor w i j) := by
  intro r c hrc
  by_cases hci : c = i
  · subst c
    have hrj : r ≠ j := ne_of_lt (lt_trans hrc hij)
    simp [factor, factorColumn, hbefore r hrc, basis, hrj]
  by_cases hcj : c = j
  · subst c
    simp [factor, factorColumn, ne_of_gt hij, basis, ne_of_lt hrc]
  · by_cases hrj : r = j
    · subst r
      simp [factor, factorColumn, hci, hcj, hafter c hrc, basis, ne_of_lt hrc]
    · simp [factor, factorColumn, hci, hcj, basis, ne_of_lt hrc, hrj]

theorem factor_diagonal (w : I → ℚ) (i j c : I) (hij : i ≠ j) :
    factor w i j c c = if c = i then w i else if c = j then alpha w j else 1 := by
  by_cases hci : c = i
  · subst c
    simp [factor, factorColumn, basis, hij]
  by_cases hcj : c = j
  · subst c
    simp [factor, factorColumn, basis, hij.symm]
  · simp [factor, factorColumn, basis, hci, hcj]

theorem factor_isUnit (w : I → ℚ) (i j : I) (hij : i < j)
    (hi : w i ≠ 0) (hj : w j ≠ 0) (hn : normSq w ≠ 0)
    (hbefore : ∀ r, r < i → w r = 0)
    (hafter : ∀ r, j < r → w r = 0) :
    IsUnit (factor w i j) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  have htri : (factor w i j).BlockTriangular OrderDual.toDual := by
    intro r c hrc
    exact factor_lower w i j hij hbefore hafter r c hrc
  rw [Matrix.det_of_lowerTriangular _ htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro c _
  rw [factor_diagonal w i j c (ne_of_lt hij)]
  split_ifs
  · exact hi
  · exact div_ne_zero (neg_ne_zero.mpr hn) (mul_ne_zero (by norm_num) hj)
  · exact one_ne_zero

/-- Explicit triangular conjugation, suitable for the scan implementation. -/
theorem reflection_eq_conjugate (w : I → ℚ) (i j : I) (hij : i < j)
    (hi : w i ≠ 0) (hj : w j ≠ 0) (hn : normSq w ≠ 0)
    (hbefore : ∀ r, r < i → w r = 0)
    (hafter : ∀ r, j < r → w r = 0) :
    reflection w = factor w i j * swapMatrix i j * (factor w i j)⁻¹ := by
  have hunit := factor_isUnit w i j hij hi hj hn hbefore hafter
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  calc
    reflection w = (reflection w * factor w i j) * (factor w i j)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    _ = factor w i j * swapMatrix i j * (factor w i j)⁻¹ := by
      rw [reflection_mul_factor w i j (ne_of_lt hij) hn hj]

theorem factor_inverse_lower (w : I → ℚ) (i j : I) (hij : i < j)
    (hi : w i ≠ 0) (hj : w j ≠ 0) (hn : normSq w ≠ 0)
    (hbefore : ∀ r, r < i → w r = 0)
    (hafter : ∀ r, j < r → w r = 0) :
    LowerTriangular ((factor w i j)⁻¹) := by
  have hunit := factor_isUnit w i j hij hi hj hn hbefore hafter
  letI := hunit.nonempty_invertible.some
  have htri : (factor w i j).BlockTriangular OrderDual.toDual := by
    intro r c hrc
    exact factor_lower w i j hij hbefore hafter r c hrc
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular htri
  exact fun r c hrc => hinv hrc

omit [LinearOrder I] in
/-- A nonzero rational coordinate forces positive squared Euclidean length. -/
theorem normSq_ne_zero_of_coordinate (w : I → ℚ) (j : I) (hj : w j ≠ 0) :
    normSq w ≠ 0 := by
  intro hn
  have hsum : (∑ k : I, w k * w k) = 0 := hn
  have hnonneg : ∀ k ∈ (Finset.univ : Finset I), 0 ≤ w k * w k :=
    fun k _ => mul_self_nonneg (w k)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hz with h | h <;> exact hj h

/-- The reflection direction for a one-dimensional field interchange. The
lexicographic sum puts every H coordinate before every D coordinate. -/
def doubleVec (u : I → ℚ) : I ⊕ₗ I → ℚ :=
  Sum.elim u (fun k => -u k)

omit [LinearOrder I] in
theorem normSq_doubleVec (u : I → ℚ) :
    normSq (doubleVec u) = 2 * normSq u := by
  change (∑ k : I ⊕ I, doubleVec u k * doubleVec u k) = 2 * normSq u
  rw [Fintype.sum_sum_type]
  simp only [doubleVec, Sum.elim_inl, Sum.elim_inr, neg_mul_neg]
  change normSq u + normSq u = 2 * normSq u
  ring

/-- The actual rational rank-one orthogonal projection associated with `u`. -/
def lineProjection (u : I → ℚ) : Matrix I I ℚ :=
  (normSq u)⁻¹ • Matrix.vecMulVec u u

-- Use the same equality decision as the generic ordered-index theorems.
-- This avoids two definitionally different inverses for the Lex type synonym.
local instance doubledDecEq : DecidableEq (I ⊕ₗ I) :=
  (inferInstance : LinearOrder (I ⊕ₗ I)).toDecidableEq

/-- The two-bank partial swap, in the physical H-before-D coordinate order. -/
def partialSwap (P : Matrix I I ℚ) : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ :=
  Matrix.fromBlocks (1-P) P P (1-P)

/-- The field-swap matrix is exactly the reflection to which the preceding
triangular factorization applies. -/
theorem reflection_doubleVec (u : I → ℚ) (hn : normSq u ≠ 0) :
    reflection (doubleVec u) = partialSwap (lineProjection u) := by
  rw [reflection, normSq_doubleVec]
  have h2 : (2:ℚ) * normSq u ≠ 0 := mul_ne_zero two_ne_zero hn
  ext a b
  change ((1 : Matrix (I ⊕ I) (I ⊕ I) ℚ) - (2 / (2 * normSq u)) •
      Matrix.vecMulVec (Sum.elim u (fun k => -u k)) (Sum.elim u (fun k => -u k))) a b =
    Matrix.fromBlocks (1 - lineProjection u) (lineProjection u) (lineProjection u)
      (1 - lineProjection u) a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [lineProjection, Matrix.one_apply, Matrix.vecMulVec_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    field_simp <;> (try split_ifs) <;> ring

/-- Concrete specialization: one cross-bank transposition between the first
and last support positions, surrounded by lower-triangular rational maps. -/
theorem partialSwap_eq_conjugate (u : I → ℚ) (s t : I)
    (hs : u s ≠ 0) (ht : u t ≠ 0)
    (hbefore : ∀ r, r < s → u r = 0)
    (hafter : ∀ r, t < r → u r = 0) :
    let w := doubleVec u
    let i : I ⊕ₗ I := toLex (Sum.inl s)
    let j : I ⊕ₗ I := toLex (Sum.inr t)
    partialSwap (lineProjection u) = factor w i j * swapMatrix i j * (factor w i j)⁻¹ := by
  try dsimp only
  have hnorm : normSq u ≠ 0 := normSq_ne_zero_of_coordinate u s hs
  have hi : doubleVec u (toLex (Sum.inl s)) ≠ 0 := hs
  have hj : doubleVec u (toLex (Sum.inr t)) ≠ 0 := neg_ne_zero.mpr ht
  have hn : normSq (doubleVec u) ≠ 0 :=
    normSq_ne_zero_of_coordinate _ (toLex (Sum.inl s)) hi
  have hfirst : ∀ r : I ⊕ₗ I, r < toLex (Sum.inl s) → doubleVec u r = 0 := by
    rintro (r | r) h
    · exact hbefore r (Sum.Lex.inl_lt_inl_iff.mp h)
    · exact (Sum.Lex.not_inr_lt_inl h).elim
  have hlast : ∀ r : I ⊕ₗ I, toLex (Sum.inr t) < r → doubleVec u r = 0 := by
    rintro (r | r) h
    · exact (Sum.Lex.not_inr_lt_inl h).elim
    · exact neg_eq_zero.mpr (hafter r (Sum.Lex.inr_lt_inr_iff.mp h))
  rw [← reflection_doubleVec u hnorm]
  exact reflection_eq_conjugate (doubleVec u) (toLex (Sum.inl s)) (toLex (Sum.inr t))
    (Sum.Lex.inl_lt_inr s t) hi hj hn hfirst hlast

/-- A finite nonzero vector has first and last support positions. -/
theorem exists_support_extremes (u : I → ℚ) (hu : u ≠ 0) :
    ∃ s t, u s ≠ 0 ∧ u t ≠ 0 ∧
      (∀ r, r < s → u r = 0) ∧ (∀ r, t < r → u r = 0) := by
  classical
  let support := Finset.univ.filter (fun k => u k ≠ 0)
  have hne : support.Nonempty := by
    by_contra h
    apply hu
    ext k
    by_contra hk
    apply h
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image support id hne
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image support id hne
  refine ⟨s, t, (Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp ht).2, ?_, ?_⟩
  · intro r hrs
    by_contra hr
    have hmem : r ∈ support := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
    exact (not_le_of_gt hrs) (hmin r hmem)
  · intro r htr
    by_contra hr
    have hmem : r ∈ support := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩
    exact (not_le_of_gt htr) (hmax r hmem)

/-- Existence with no additional algebraic assumptions on the nonzero line
vector: a rank-one partial swap uses one explicit H-to-D transposition. -/
theorem exists_partialSwap_conjugacy (u : I → ℚ) (hu : u ≠ 0) :
    ∃ s t : I,
      partialSwap (lineProjection u) =
        factor (doubleVec u) (toLex (Sum.inl s)) (toLex (Sum.inr t)) *
          swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t)) *
          (factor (doubleVec u) (toLex (Sum.inl s)) (toLex (Sum.inr t)))⁻¹ := by
  obtain ⟨s, t, hs, ht, hbefore, hafter⟩ := exists_support_extremes u hu
  exact ⟨s, t, partialSwap_eq_conjugate u s t hs ht hbefore hafter⟩

omit [Fintype I] in
theorem doubleVec_support_bounds (u : I → ℚ) (s t : I)
    (hbefore : ∀ r, r < s → u r = 0)
    (hafter : ∀ r, t < r → u r = 0) :
    (∀ r : I ⊕ₗ I, r < toLex (Sum.inl s) → doubleVec u r = 0) ∧
    (∀ r : I ⊕ₗ I, toLex (Sum.inr t) < r → doubleVec u r = 0) := by
  constructor
  · rintro (r | r) h
    · exact hbefore r (Sum.Lex.inl_lt_inl_iff.mp h)
    · exact (Sum.Lex.not_inr_lt_inl h).elim
  · rintro (r | r) h
    · exact (Sum.Lex.not_inr_lt_inl h).elim
    · exact neg_eq_zero.mpr (hafter r (Sum.Lex.inr_lt_inr_iff.mp h))

/-- Both actual field-swap factors have the triangular and invertibility
properties required by the sequential coordinate-update implementation. -/
theorem partialSwap_factor_properties (u : I → ℚ) (s t : I)
    (hs : u s ≠ 0) (ht : u t ≠ 0)
    (hbefore : ∀ r, r < s → u r = 0)
    (hafter : ∀ r, t < r → u r = 0) :
    let L := factor (doubleVec u) (toLex (Sum.inl s)) (toLex (Sum.inr t))
    LowerTriangular L ∧ IsUnit L ∧ LowerTriangular L⁻¹ := by
  try dsimp only
  have hi : doubleVec u (toLex (Sum.inl s)) ≠ 0 := hs
  have hj : doubleVec u (toLex (Sum.inr t)) ≠ 0 := neg_ne_zero.mpr ht
  have hn := normSq_ne_zero_of_coordinate _ (toLex (Sum.inl s)) hi
  obtain ⟨hfirst, hlast⟩ := doubleVec_support_bounds u s t hbefore hafter
  exact ⟨factor_lower _ _ _ (Sum.Lex.inl_lt_inr s t) hfirst hlast,
    factor_isUnit _ _ _ (Sum.Lex.inl_lt_inr s t) hi hj hn hfirst hlast,
    factor_inverse_lower _ _ _ (Sum.Lex.inl_lt_inr s t) hi hj hn hfirst hlast⟩

theorem lower_diagonal_nonzero (A : Matrix I I ℚ)
    (hA : LowerTriangular A) (hu : IsUnit A) : ∀ k, A k k ≠ 0 := by
  have htri : A.BlockTriangular OrderDual.toDual := fun {r c} hrc => hA r c hrc
  have hd := ((Matrix.isUnit_iff_isUnit_det A).mp hu).ne_zero
  rw [Matrix.det_of_lowerTriangular A htri] at hd
  exact fun k => (Finset.prod_ne_zero_iff.mp hd) k (Finset.mem_univ k)

/-- Any principal submatrix selected in increasing order from a lower
triangular unit is itself lower triangular and invertible. -/
theorem lower_submatrix_unit {J : Type*} [Fintype J] [LinearOrder J]
    (A : Matrix I I ℚ) (hA : LowerTriangular A) (hu : IsUnit A)
    (f : J → I) (hf : StrictMono f) :
    LowerTriangular (A.submatrix f f) ∧ IsUnit (A.submatrix f f) := by
  have hlow : LowerTriangular (A.submatrix f f) :=
    fun r c hrc => hA (f r) (f c) (hf hrc)
  refine ⟨hlow, ?_⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  have htri : (A.submatrix f f).BlockTriangular OrderDual.toDual :=
    fun {r c} hrc => hlow r c hrc
  rw [Matrix.det_of_lowerTriangular _ htri]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => lower_diagonal_nonzero A hA hu (f k))

def highBlock (A : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ) : Matrix I I ℚ :=
  A.submatrix (fun k => toLex (Sum.inl k)) (fun k => toLex (Sum.inl k))

def lowBlock (A : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ) : Matrix I I ℚ :=
  A.submatrix (fun k => toLex (Sum.inr k)) (fun k => toLex (Sum.inr k))

def crossBlock (A : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ) : Matrix I I ℚ :=
  A.submatrix (fun k => toLex (Sum.inr k)) (fun k => toLex (Sum.inl k))

omit [Fintype I] in
/-- The exact block form consumed by `PartialSwapScan.lowerBlockProgram`. -/
theorem lower_blockForm (A : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ)
    (hA : LowerTriangular A) :
    A = Matrix.fromBlocks (highBlock A) 0 (crossBlock A) (lowBlock A) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rfl
  · exact hA (toLex (Sum.inl a)) (toLex (Sum.inr b)) (Sum.Lex.inl_lt_inr a b)
  · rfl
  · rfl

/-- The H and D diagonal blocks of either triangular scan factor are valid
lower-triangular units.  The off-diagonal block may be handled by cross scans. -/
theorem lower_diagonalBlocks (A : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ)
    (hA : LowerTriangular A) (hu : IsUnit A) :
    (LowerTriangular (highBlock A) ∧ IsUnit (highBlock A)) ∧
    (LowerTriangular (lowBlock A) ∧ IsUnit (lowBlock A)) := by
  exact ⟨lower_submatrix_unit A hA hu (fun k => toLex (Sum.inl k)) Sum.Lex.inl_strictMono,
    lower_submatrix_unit A hA hu (fun k => toLex (Sum.inr k)) Sum.Lex.inr_strictMono⟩

/-- The complete algebraic interface: an arbitrary nonzero line provides one
H-to-D transposition surrounded by invertible lower-triangular factors. -/
theorem exists_partialSwap_scan_factors (u : I → ℚ) (hu : u ≠ 0) :
    ∃ s t : I,
      let L := factor (doubleVec u) (toLex (Sum.inl s)) (toLex (Sum.inr t))
      LowerTriangular L ∧ IsUnit L ∧ LowerTriangular L⁻¹ ∧
      partialSwap (lineProjection u) = L *
        swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t)) * L⁻¹ := by
  obtain ⟨s, t, hs, ht, hbefore, hafter⟩ := exists_support_extremes u hu
  obtain ⟨hlow, hunit, hinv⟩ := partialSwap_factor_properties u s t hs ht hbefore hafter
  exact ⟨s, t, hlow, hunit, hinv, partialSwap_eq_conjugate u s t hs ht hbefore hafter⟩

end CSL.Construction.TriangularConjugacy


