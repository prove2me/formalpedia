-- Prove2me | Definitions.Def_CSL_Circuit_Labels_ProjectionRankDecomposition
-- name    : CSL_Circuit_Labels_ProjectionRankDecomposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:52.281509+00:00
-- url     : https://prove2.me/theorems/b3415982-6d36-47fa-a923-d3ed66135fca
-- title:
--   Coded sorting library: Circuit / Labels / ProjectionRankDecomposition
-- statement:
--   Module `CodedSorting.Circuit.Labels.ProjectionRankDecomposition` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Rational orthogonal projections and their exact rank budget
--
--   The matrix identities in this file connect an orthogonal decomposition into
--   one-dimensional projections with a product of ordinary rank-one partial swaps.
--   The final index set is `Fin P.rank`, not an unspecified finite family.
--
--   This file does not by itself assert an external-memory program or its cost.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Labels.ProjectionRankDecomposition

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_TriangularConjugacy
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Rational orthogonal projections and their exact rank budget

The matrix identities in this file connect an orthogonal decomposition into
one-dimensional projections with a product of ordinary rank-one partial swaps.
The final index set is `Fin P.rank`, not an unspecified finite family.

This file does not by itself assert an external-memory program or its cost.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CSL.Construction.ProjectionRankDecomposition

open scoped BigOperators Matrix
open TriangularConjugacy

variable {I : Type*} [Fintype I] [LinearOrder I]

local instance doubledDecEq : DecidableEq (I ⊕ₗ I) :=
  (inferInstance : LinearOrder (I ⊕ₗ I)).toDecidableEq

omit [LinearOrder I] in
theorem lineProjection_mulVec (u x : I → ℚ) :
    lineProjection u *ᵥ x = ((normSq u)⁻¹ * (u ⬝ᵥ x)) • u := by
  ext r
  simp only [lineProjection, Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [LinearOrder I] in
theorem lineProjection_self (u : I → ℚ) (hu : normSq u ≠ 0) :
    lineProjection u *ᵥ u = u := by
  rw [lineProjection_mulVec]
  change ((normSq u)⁻¹ * normSq u) • u = u
  simp [hu]

theorem lineProjection_mul_zero (u v : I → ℚ) (h : u ⬝ᵥ v = 0) :
    lineProjection u * lineProjection v = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, lineProjection_mulVec v,
    Matrix.mulVec_smul, lineProjection_mulVec u v, h]
  simp [Matrix.zero_mulVec, Pi.zero_apply]
  rfl

theorem lineProjection_idempotent (u : I → ℚ) (hu : normSq u ≠ 0) :
    lineProjection u * lineProjection u = lineProjection u := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, lineProjection_mulVec u (Pi.single j 1),
    Matrix.mulVec_smul, lineProjection_self u hu]

omit [LinearOrder I] in
theorem lineProjection_symmetric (u : I → ℚ) :
    (lineProjection u)ᵀ = lineProjection u := by
  ext i j
  simp [lineProjection, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]

omit [Fintype I] in
@[simp] theorem partialSwap_zero :
    partialSwap (0 : Matrix I I ℚ) = 1 := by
  ext r c
  rw [Matrix.one_apply]
  change (Matrix.fromBlocks (1 - 0) 0 0 (1 - 0) : Matrix (I ⊕ I) (I ⊕ I) ℚ) r c = _
  rcases r with r | r <;> rcases c with c | c
  · split_ifs with h'
    · obtain rfl : r = c := Sum.inl_injective h'
      simp
    · have hrc : r ≠ c := fun e => h' (e ▸ rfl)
      simp [Matrix.one_apply, hrc]
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    exact (if_neg Sum.inl_ne_inr).symm
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    exact (if_neg Sum.inr_ne_inl).symm
  · split_ifs with h'
    · obtain rfl : r = c := Sum.inr_injective h'
      simp
    · have hrc : r ≠ c := fun e => h' (e ▸ rfl)
      simp [Matrix.one_apply, hrc]

/-- Orthogonal summands combine without an extra swap. Only the ordered
product `A * B = 0` is needed for this ordered factorization. -/
theorem partialSwap_add (A B : Matrix I I ℚ) (h : A * B = 0) :
    partialSwap (A + B) = partialSwap A * partialSwap B := by
  unfold partialSwap
  change (Matrix.fromBlocks (1 - (A + B)) (A + B) (A + B) (1 - (A + B)) :
      Matrix (I ⊕ I) (I ⊕ I) ℚ) =
    (Matrix.fromBlocks (1 - A) A A (1 - A) : Matrix (I ⊕ I) (I ⊕ I) ℚ) *
      Matrix.fromBlocks (1 - B) B B (1 - B)
  rw [Matrix.fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, h, add_zero, sub_zero]
  abel_nf

/-- A one-column left inverse computes the actual Mathlib matrix rank. -/
theorem rank_of_split {J K : Type*} [Fintype J] [Fintype K] [DecidableEq K]
    (U : Matrix J K ℚ) (V : Matrix K J ℚ) (h : V * U = 1) :
    (U * V).rank = Fintype.card K := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left U V).trans U.rank_le_card_width
  · have heq : V * ((U * V) * U) = 1 := by
      calc
        V * ((U * V) * U) = (V * U) * (V * U) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h]; simp
    calc
      Fintype.card K = (1 : Matrix K K ℚ).rank := Matrix.rank_one.symm
      _ = (V * ((U * V) * U)).rank := by rw [heq]
      _ ≤ ((U * V) * U).rank := Matrix.rank_mul_le_right _ _
      _ ≤ (U * V).rank := Matrix.rank_mul_le_left _ _

omit [LinearOrder I] in
theorem lineProjection_rank (u : I → ℚ) (hu : normSq u ≠ 0) :
    (lineProjection u).rank = 1 := by
  let U : Matrix I Unit ℚ := fun i _ => u i
  let V : Matrix Unit I ℚ := fun _ j => (normSq u)⁻¹ * u j
  have hVU : V * U = 1 := by
    ext i j
    have hsum : (V * U) i j = (normSq u)⁻¹ * normSq u := by
      rw [Matrix.mul_apply]
      simp only [U, V, normSq, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hsum]
    simp [hu, Matrix.one_apply]
  have hUV : U * V = lineProjection u := by
    ext i j
    rw [Matrix.mul_apply]
    simp [U, V, lineProjection, Matrix.vecMulVec_apply,
      mul_comm, mul_left_comm, mul_assoc]
  rw [← hUV, rank_of_split U V hVU]
  rfl

/-- Dot product as a rational bilinear form, used only to choose a basis. -/
def dotForm : LinearMap.BilinForm ℚ (I → ℚ) :=
  Matrix.toBilin' (1 : Matrix I I ℚ)

@[simp] theorem dotForm_apply (x y : I → ℚ) : dotForm x y = x ⬝ᵥ y := by
  simp [dotForm, Matrix.toBilin'_apply']

theorem dotForm_symmetric : LinearMap.IsSymm (dotForm (I := I)) := by
  rw [LinearMap.isSymm_def]
  intro x y
  simp only [RingHom.id_apply, dotForm_apply]
  exact dotProduct_comm x y

/-- The image of any rational matrix has a dot-orthogonal basis indexed by
its actual Mathlib rank. No projection assumption is used for this step. -/
theorem exists_orthogonal_range_basis (P : Matrix I I ℚ) :
    ∃ b : Module.Basis (Fin P.rank) ℚ (LinearMap.range P.mulVecLin),
      ∀ i j, i ≠ j → (b i : I → ℚ) ⬝ᵥ (b j : I → ℚ) = 0 := by
  let V := LinearMap.range P.mulVecLin
  let B : LinearMap.BilinForm ℚ V := (dotForm (I := I)).domRestrict₁₂ V V
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hB : LinearMap.IsSymm B := by
    rw [LinearMap.isSymm_def]
    intro x y
    simp only [B, RingHom.id_apply, LinearMap.domRestrict₁₂_apply, dotForm_apply]
    exact dotProduct_comm _ _
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  refine ⟨b, ?_⟩
  intro i j hij
  have h := hb hij
  change B (b i) (b j) = 0 at h
  simp only [B, LinearMap.domRestrict₁₂_apply, dotForm_apply] at h
  exact h

omit [LinearOrder I] in
theorem range_fixed (P : Matrix I I ℚ) (hP : P * P = P)
    (v : LinearMap.range P.mulVecLin) : P *ᵥ (v : I → ℚ) = v := by
  obtain ⟨x, hx⟩ := v.property
  change P *ᵥ x = (v : I → ℚ) at hx
  rw [← hx, Matrix.mulVec_mulVec, hP]

omit [LinearOrder I] in
theorem normSq_ne_zero (u : I → ℚ) (hu : u ≠ 0) : normSq u ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  exact normSq_ne_zero_of_coordinate u i hi

omit [LinearOrder I] in
theorem sum_mulVec {J : Type*} [Fintype J] (A : J → Matrix I I ℚ) (x : I → ℚ) :
    (∑ j, A j) *ᵥ x = ∑ j, A j *ᵥ x := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

omit [LinearOrder I] in
/-- The sum of the line projections of an orthogonal basis is the identity on
the subspace spanned by that basis. -/
theorem orthogonal_basis_projection_sum {J : Type*} [Fintype J] [DecidableEq J]
    (W : Submodule ℚ (I → ℚ)) (b : Module.Basis J ℚ W)
    (ho : ∀ i j, i ≠ j → (b i : I → ℚ) ⬝ᵥ (b j : I → ℚ) = 0) :
    ∀ y : W, (∑ i, lineProjection (b i : I → ℚ)) *ᵥ (y : I → ℚ) = y := by
  let R := ∑ i, lineProjection (b i : I → ℚ)
  have hn (i : J) : normSq (b i : I → ℚ) ≠ 0 :=
    normSq_ne_zero _ (fun h => b.ne_zero i (Subtype.ext h))
  have hfix (j : J) : R *ᵥ (b j : I → ℚ) = b j := by
    change (∑ i, lineProjection (b i : I → ℚ)) *ᵥ (b j : I → ℚ) = b j
    rw [sum_mulVec]
    calc
      (∑ i, lineProjection (b i : I → ℚ) *ᵥ (b j : I → ℚ)) =
          lineProjection (b j : I → ℚ) *ᵥ (b j : I → ℚ) := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          rw [lineProjection_mulVec, ho i j hij]
          simp
        · simp
      _ = b j := lineProjection_self _ (hn j)
  have hlin : R.mulVecLin.comp W.subtype = W.subtype := b.ext hfix
  intro y
  exact LinearMap.congr_fun hlin y

/-- Symmetry and idempotence turn the range's orthogonal basis into a
decomposition of the full projection matrix. -/
theorem orthogonal_range_basis_sum (P : Matrix I I ℚ)
    (hs : Pᵀ = P) (hp : P * P = P)
    (b : Module.Basis (Fin P.rank) ℚ (LinearMap.range P.mulVecLin))
    (ho : ∀ i j, i ≠ j → (b i : I → ℚ) ⬝ᵥ (b j : I → ℚ) = 0) :
    (∑ i, lineProjection (b i : I → ℚ)) = P := by
  let R := ∑ i, lineProjection (b i : I → ℚ)
  have hR := orthogonal_basis_projection_sum (LinearMap.range P.mulVecLin) b ho
  have hRP (x : I → ℚ) : R *ᵥ (P *ᵥ x) = R *ᵥ x := by
    change (∑ i, lineProjection (b i : I → ℚ)) *ᵥ (P *ᵥ x) =
      (∑ i, lineProjection (b i : I → ℚ)) *ᵥ x
    rw [sum_mulVec, sum_mulVec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [lineProjection_mulVec, lineProjection_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, range_fixed P hp]
  apply Matrix.ext_of_mulVec_single
  intro j
  exact (hRP (Pi.single j 1)).symm.trans
    (hR ⟨P *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩)

/-- An exact-rank decomposition, retaining rational vectors as the inputs to
the constructive triangular-conjugacy lemmas. -/
structure RankDecomposition (P : Matrix I I ℚ) where
  vectors : Fin P.rank → I → ℚ
  nonzero : ∀ i, vectors i ≠ 0
  orthogonal : ∀ i j, i ≠ j → vectors i ⬝ᵥ vectors j = 0
  sum_eq : (∑ i, lineProjection (vectors i)) = P

/-- Every rational symmetric idempotent matrix has exactly `P.rank` pairwise
orthogonal nonzero rational directions. This includes the rank-zero case. -/
theorem exists_rank_decomposition (P : Matrix I I ℚ)
    (hs : Pᵀ = P) (hp : P * P = P) : Nonempty (RankDecomposition P) := by
  obtain ⟨b, hb⟩ := exists_orthogonal_range_basis P
  refine ⟨{
    vectors := fun i => (b i : I → ℚ)
    nonzero := fun i h => b.ne_zero i (Subtype.ext h)
    orthogonal := hb
    sum_eq := orthogonal_range_basis_sum P hs hp b hb
  }⟩

omit [LinearOrder I] in
theorem RankDecomposition.projection_rank {P : Matrix I I ℚ}
    (d : RankDecomposition P) (i : Fin P.rank) :
    (lineProjection (d.vectors i)).rank = 1 :=
  lineProjection_rank _ (normSq_ne_zero _ (d.nonzero i))

theorem RankDecomposition.projection_orthogonal {P : Matrix I I ℚ}
    (d : RankDecomposition P) (i j : Fin P.rank) (hij : i ≠ j) :
    lineProjection (d.vectors i) * lineProjection (d.vectors j) = 0 :=
  lineProjection_mul_zero _ _ (d.orthogonal i j hij)

omit [LinearOrder I] in
theorem matrix_mul_list_sum_zero {J : Type*} (A : Matrix I I ℚ)
    (Q : J → Matrix I I ℚ) (l : List J)
    (h : ∀ j ∈ l, A * Q j = 0) : A * (l.map Q).sum = 0 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.mul_add]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk])), zero_add]

/-- An ordered product; no commutative-matrix product notation is used. -/
theorem partialSwap_list_sum {J : Type*} (Q : J → Matrix I I ℚ)
    (ho : ∀ i j, i ≠ j → Q i * Q j = 0) (l : List J) (hn : l.Nodup) :
    partialSwap (l.map Q).sum = (l.map (fun i => partialSwap (Q i))).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨hin, hnl⟩ := List.nodup_cons.mp hn
    have hz : Q i * (l.map Q).sum = 0 :=
      matrix_mul_list_sum_zero (Q i) Q l (by
        intro j hj
        apply ho i j
        intro hij
        exact hin (hij.symm ▸ hj))
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    rw [partialSwap_add _ _ hz, ih hnl]

/-- The ordered list has one factor for each actual rank unit. -/
noncomputable def RankDecomposition.factors {P : Matrix I I ℚ} (d : RankDecomposition P) :
    List (Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ) :=
  List.ofFn (fun i => partialSwap (lineProjection (d.vectors i)))

@[simp] theorem RankDecomposition.factors_length {P : Matrix I I ℚ}
    (d : RankDecomposition P) : d.factors.length = P.rank := by
  simp [RankDecomposition.factors]

/-- Exactly `P.rank` rank-one partial swaps implement the arbitrary projection's
partial swap, with matrix multiplication in the displayed list order. -/
theorem RankDecomposition.factors_prod {P : Matrix I I ℚ}
    (d : RankDecomposition P) : d.factors.prod = partialSwap P := by
  have h := partialSwap_list_sum (fun i => lineProjection (d.vectors i))
    d.projection_orthogonal (List.finRange P.rank) (List.nodup_finRange P.rank)
  rw [← Fin.sum_univ_def, d.sum_eq] at h
  simpa only [RankDecomposition.factors, List.ofFn_eq_map] using h.symm

/-- The reverse product is the same partial swap, so both the standard matrix
product convention and chronological application have the stated endpoint. -/
theorem RankDecomposition.factors_reverse_prod {P : Matrix I I ℚ}
    (d : RankDecomposition P) : d.factors.reverse.prod = partialSwap P := by
  have h := partialSwap_list_sum (fun i => lineProjection (d.vectors i))
    d.projection_orthogonal (List.finRange P.rank).reverse
    (by simpa using List.nodup_finRange P.rank)
  rw [List.map_reverse, List.sum_reverse, ← Fin.sum_univ_def, d.sum_eq] at h
  simpa only [RankDecomposition.factors, List.ofFn_eq_map, List.map_reverse] using h.symm

/-- Every one of those exact-rank factors is a single H-to-D transposition
between invertible lower-triangular scan factors. -/
theorem RankDecomposition.component_scan_factors {P : Matrix I I ℚ}
    (d : RankDecomposition P) (i : Fin P.rank) :
    ∃ s t : I,
      let L := factor (doubleVec (d.vectors i)) (toLex (Sum.inl s)) (toLex (Sum.inr t))
      LowerTriangular L ∧ IsUnit L ∧ LowerTriangular L⁻¹ ∧
      partialSwap (lineProjection (d.vectors i)) = L *
        swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t)) * L⁻¹ :=
  exists_partialSwap_scan_factors _ (d.nonzero i)

/-- Existence, exact factor count, and the resulting partial-swap matrix in one
interface. The individual factors are exposed by `d.vectors`. -/
theorem exists_exact_rank_partialSwap_product (P : Matrix I I ℚ)
    (hs : Pᵀ = P) (hp : P * P = P) :
    ∃ d : RankDecomposition P,
      d.factors.length = P.rank ∧ d.factors.prod = partialSwap P := by
  obtain ⟨d⟩ := exists_rank_decomposition P hs hp
  exact ⟨d, d.factors_length, d.factors_prod⟩

end CSL.Construction.ProjectionRankDecomposition


