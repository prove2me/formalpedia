-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:39:56.65692+00:00
-- url     : https://prove2.me/theorems/01389cb4-2409-4874-b5db-6babeb6bec57
-- title:
--   Congruence
-- statement:
--   Definitions and structural lemmas for Congruence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/Congruence.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_adjoin_eq_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_one_add_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def indexPolynomialEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    PolynomialRing P →+* ResidueField P r level :=
  (Polynomial.aeval (indexPlaceY P r level)).toRingHom
@[simp] theorem indexPolynomialEval_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexPolynomialEval P r level Polynomial.X =
      indexPlaceY P r level := by
  simp [indexPolynomialEval]
@[simp] theorem indexPolynomialEval_one_add_X
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexPolynomialEval P r level (1 + Polynomial.X) =
      1 + indexPlaceY P r level := by
  simp [indexPolynomialEval]
theorem indexPolynomialEval_denominator_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexPolynomialEval P r level
      (Polynomial.X * (1 + Polynomial.X))) := by
  rw [map_mul, indexPolynomialEval_X, indexPolynomialEval_one_add_X,
    isUnit_iff_ne_zero]
  exact mul_ne_zero (indexPlaceY_ne_zero P r level)
    (indexPlaceY_one_add_ne_zero P r level)
noncomputable def indexArithmeticEval
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P →+* ResidueField P r level :=
  IsLocalization.Away.lift
    (Polynomial.X * (1 + Polynomial.X) : PolynomialRing P)
    (S := ArithmeticRing P)
    (g := indexPolynomialEval P r level)
    (indexPolynomialEval_denominator_isUnit P r level)
@[simp] theorem indexArithmeticEval_algebraMap
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    indexArithmeticEval P r level
        (algebraMap (PolynomialRing P) (ArithmeticRing P) f) =
      indexPolynomialEval P r level f := by
  exact IsLocalization.Away.lift_eq _ _ _
theorem indexPolynomialEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexPolynomialEval P r level) := by
  change Function.Surjective
    ((Polynomial.aeval (indexPlaceY P r level) :
      PolynomialRing P →ₐ[BaseField P] ResidueField P r level).toRingHom)
  have hRange :
      (Polynomial.aeval (indexPlaceY P r level) :
        PolynomialRing P →ₐ[BaseField P]
          ResidueField P r level).range = ⊤ := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic (indexPlaceY P r level))
      (indexPlaceY_adjoin_eq_top P r level)
  exact (AlgHom.range_eq_top _).mp hRange
theorem indexArithmeticEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexArithmeticEval P r level) := by
  intro x
  obtain ⟨f, rfl⟩ := indexPolynomialEval_surjective P r level x
  exact ⟨algebraMap (PolynomialRing P) (ArithmeticRing P) f,
    indexArithmeticEval_algebraMap P r level f⟩
noncomputable def IndexCongruenceIdeal
    (P : BasePrime) (r : Rank) (level : Nat) :
    Ideal (ArithmeticRing P) :=
  RingHom.ker (indexArithmeticEval P r level)
noncomputable def indexArithmeticQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    ArithmeticRing P ⧸ IndexCongruenceIdeal P r level ≃+*
      ResidueField P r level :=
  RingHom.quotientKerEquivOfSurjective
    (indexArithmeticEval_surjective P r level)
namespace CongruenceLifting
open Matrix
theorem property_six_mul
    {M : Type*} [Monoid M] (Q : M → Prop)
    (hmul : ∀ a b, Q a → Q b → Q (a * b))
    {a b c d e f : M}
    (ha : Q a) (hb : Q b) (hc : Q c)
    (hd : Q d) (he : Q e) (hf : Q f) :
    Q (a * b * c * d * e * f) :=
  hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ha hb) hc) hd) he) hf
theorem field_mul_transvection_apply
    {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (i j row col : Fin n) (c : K) :
    (M * transvection i j c) row col =
      if col = j then M row j + c * M row i else M row col := by
  by_cases h : col = j
  · subst col
    rw [if_pos rfl]
    exact Matrix.mul_transvection_apply_same i j row c M
  · rw [if_neg h]
    exact Matrix.mul_transvection_apply_of_ne i j row col h c M
theorem fin3_pair02_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (0 : Fin 3) (2 : Fin 3) a *
      transvection (2 : Fin 3) (0 : Fin 3) (-a⁻¹) *
      transvection (0 : Fin 3) (2 : Fin 3) a *
      transvection (0 : Fin 3) (2 : Fin 3) (-1) *
      transvection (2 : Fin 3) (0 : Fin 3) 1 *
      transvection (0 : Fin 3) (2 : Fin 3) (-1) =
        diagonal ![a, 1, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]
theorem fin3_pair12_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (1 : Fin 3) (2 : Fin 3) a *
      transvection (2 : Fin 3) (1 : Fin 3) (-a⁻¹) *
      transvection (1 : Fin 3) (2 : Fin 3) a *
      transvection (1 : Fin 3) (2 : Fin 3) (-1) *
      transvection (2 : Fin 3) (1 : Fin 3) 1 *
      transvection (1 : Fin 3) (2 : Fin 3) (-1) =
        diagonal ![1, a, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]
theorem fin3_diagonal_eq_pair_product
    {K : Type*} [Field K] (D : Fin 3 → K)
    (hdet : Matrix.det (diagonal D) = 1) :
    diagonal D =
      diagonal ![D 0, 1, (D 0)⁻¹] *
        diagonal ![1, D 1, (D 1)⁻¹] := by
  have hprod : D 0 * (D 1 * D 2) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h2 : D 2 = (D 0)⁻¹ * (D 1)⁻¹ := by
    apply (mul_left_cancel₀ (mul_ne_zero h0 h1))
    calc
      (D 0 * D 1) * D 2 = 1 := by simpa [mul_assoc] using hprod
      _ = (D 0 * D 1) * ((D 0)⁻¹ * (D 1)⁻¹) := by
        field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h2]
theorem fin4_pair03_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (0 : Fin 4) (3 : Fin 4) a *
      transvection (3 : Fin 4) (0 : Fin 4) (-a⁻¹) *
      transvection (0 : Fin 4) (3 : Fin 4) a *
      transvection (0 : Fin 4) (3 : Fin 4) (-1) *
      transvection (3 : Fin 4) (0 : Fin 4) 1 *
      transvection (0 : Fin 4) (3 : Fin 4) (-1) =
        diagonal ![a, 1, 1, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]
theorem fin4_pair13_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (1 : Fin 4) (3 : Fin 4) a *
      transvection (3 : Fin 4) (1 : Fin 4) (-a⁻¹) *
      transvection (1 : Fin 4) (3 : Fin 4) a *
      transvection (1 : Fin 4) (3 : Fin 4) (-1) *
      transvection (3 : Fin 4) (1 : Fin 4) 1 *
      transvection (1 : Fin 4) (3 : Fin 4) (-1) =
        diagonal ![1, a, 1, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]
theorem fin4_pair23_factor
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    transvection (2 : Fin 4) (3 : Fin 4) a *
      transvection (3 : Fin 4) (2 : Fin 4) (-a⁻¹) *
      transvection (2 : Fin 4) (3 : Fin 4) a *
      transvection (2 : Fin 4) (3 : Fin 4) (-1) *
      transvection (3 : Fin 4) (2 : Fin 4) 1 *
      transvection (2 : Fin 4) (3 : Fin 4) (-1) =
        diagonal ![1, 1, a, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [field_mul_transvection_apply, Fin.reduceEq, ite_true, ite_false] <;>
    simp [transvection, Matrix.one_apply, ha]
theorem fin4_diagonal_eq_pair_product
    {K : Type*} [Field K] (D : Fin 4 → K)
    (hdet : Matrix.det (diagonal D) = 1) :
    diagonal D =
      diagonal ![D 0, 1, 1, (D 0)⁻¹] *
        diagonal ![1, D 1, 1, (D 1)⁻¹] *
          diagonal ![1, 1, D 2, (D 2)⁻¹] := by
  have hprod : D 0 * (D 1 * (D 2 * D 3)) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h2 : D 2 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h3 : D 3 = (D 0)⁻¹ * (D 1)⁻¹ * (D 2)⁻¹ := by
    apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero h0 h1) h2))
    calc
      (D 0 * D 1 * D 2) * D 3 = 1 := by
        simpa [mul_assoc] using hprod
      _ = (D 0 * D 1 * D 2) *
          ((D 0)⁻¹ * (D 1)⁻¹ * (D 2)⁻¹) := by
        field_simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h3]
theorem property_fin3_diagonal
    {K : Type*} [Field K] (Q : Matrix (Fin 3) (Fin 3) K → Prop)
    (htrans : ∀ t : Matrix.TransvectionStruct (Fin 3) K, Q t.toMatrix)
    (hmul : ∀ A B, Q A → Q B → Q (A * B))
    (D : Fin 3 → K) (hdet : Matrix.det (diagonal D) = 1) :
    Q (diagonal D) := by
  have hprod : D 0 * (D 1 * D 2) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  rw [fin3_diagonal_eq_pair_product D hdet,
    ← fin3_pair02_factor (D 0) h0,
    ← fin3_pair12_factor (D 1) h1]
  apply hmul
  · exact property_six_mul Q hmul
      (htrans ⟨0, 2, by decide, D 0⟩)
      (htrans ⟨2, 0, by decide, -(D 0)⁻¹⟩)
      (htrans ⟨0, 2, by decide, D 0⟩)
      (htrans ⟨0, 2, by decide, -1⟩)
      (htrans ⟨2, 0, by decide, 1⟩)
      (htrans ⟨0, 2, by decide, -1⟩)
  · exact property_six_mul Q hmul
      (htrans ⟨1, 2, by decide, D 1⟩)
      (htrans ⟨2, 1, by decide, -(D 1)⁻¹⟩)
      (htrans ⟨1, 2, by decide, D 1⟩)
      (htrans ⟨1, 2, by decide, -1⟩)
      (htrans ⟨2, 1, by decide, 1⟩)
      (htrans ⟨1, 2, by decide, -1⟩)
theorem property_fin4_diagonal
    {K : Type*} [Field K] (Q : Matrix (Fin 4) (Fin 4) K → Prop)
    (htrans : ∀ t : Matrix.TransvectionStruct (Fin 4) K, Q t.toMatrix)
    (hmul : ∀ A B, Q A → Q B → Q (A * B))
    (D : Fin 4 → K) (hdet : Matrix.det (diagonal D) = 1) :
    Q (diagonal D) := by
  have hprod : D 0 * (D 1 * (D 2 * D 3)) = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_succ] using hdet
  have h0 : D 0 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h1 : D 1 ≠ 0 := by
    intro h
    simp [h] at hprod
  have h2 : D 2 ≠ 0 := by
    intro h
    simp [h] at hprod
  rw [fin4_diagonal_eq_pair_product D hdet,
    ← fin4_pair03_factor (D 0) h0,
    ← fin4_pair13_factor (D 1) h1,
    ← fin4_pair23_factor (D 2) h2]
  apply hmul
  · apply hmul
    · exact property_six_mul Q hmul
        (htrans ⟨0, 3, by decide, D 0⟩)
        (htrans ⟨3, 0, by decide, -(D 0)⁻¹⟩)
        (htrans ⟨0, 3, by decide, D 0⟩)
        (htrans ⟨0, 3, by decide, -1⟩)
        (htrans ⟨3, 0, by decide, 1⟩)
        (htrans ⟨0, 3, by decide, -1⟩)
    · exact property_six_mul Q hmul
        (htrans ⟨1, 3, by decide, D 1⟩)
        (htrans ⟨3, 1, by decide, -(D 1)⁻¹⟩)
        (htrans ⟨1, 3, by decide, D 1⟩)
        (htrans ⟨1, 3, by decide, -1⟩)
        (htrans ⟨3, 1, by decide, 1⟩)
        (htrans ⟨1, 3, by decide, -1⟩)
  · exact property_six_mul Q hmul
      (htrans ⟨2, 3, by decide, D 2⟩)
      (htrans ⟨3, 2, by decide, -(D 2)⁻¹⟩)
      (htrans ⟨2, 3, by decide, D 2⟩)
      (htrans ⟨2, 3, by decide, -1⟩)
      (htrans ⟨3, 2, by decide, 1⟩)
      (htrans ⟨2, 3, by decide, -1⟩)
theorem specialLinearMap_surjective_fin3
    {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Surjective f) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 3) f) := by
  classical
  intro g
  let Q : Matrix (Fin 3) (Fin 3) K → Prop := fun M =>
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) R,
      f.mapMatrix a = M
  have htrans : ∀ t : Matrix.TransvectionStruct (Fin 3) K, Q t.toMatrix := by
    intro t
    obtain ⟨c, hc⟩ := hf t.c
    let s : Matrix.SpecialLinearGroup (Fin 3) R :=
      ⟨Matrix.transvection t.i t.j c,
        Matrix.det_transvection_of_ne t.i t.j t.hij c⟩
    refine ⟨s, ?_⟩
    ext i j
    by_cases h : t.i = i ∧ t.j = j <;>
      simp [s, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
        Matrix.map_apply, Matrix.one_apply, h, hc]
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, f.mapMatrix.map_mul, ha, hb]
  have hQ : Q (g : Matrix (Fin 3) (Fin 3) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      apply property_fin3_diagonal Q htrans hmul D
      exact hD.trans g.prop
    · exact htrans
    · exact hmul
  obtain ⟨a, ha⟩ := hQ
  refine ⟨a, Subtype.ext ?_⟩
  exact ha
theorem specialLinearMap_surjective_fin4
    {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Surjective f) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 4) f) := by
  classical
  intro g
  let Q : Matrix (Fin 4) (Fin 4) K → Prop := fun M =>
    ∃ a : Matrix.SpecialLinearGroup (Fin 4) R,
      f.mapMatrix a = M
  have htrans : ∀ t : Matrix.TransvectionStruct (Fin 4) K, Q t.toMatrix := by
    intro t
    obtain ⟨c, hc⟩ := hf t.c
    let s : Matrix.SpecialLinearGroup (Fin 4) R :=
      ⟨Matrix.transvection t.i t.j c,
        Matrix.det_transvection_of_ne t.i t.j t.hij c⟩
    refine ⟨s, ?_⟩
    ext i j
    by_cases h : t.i = i ∧ t.j = j <;>
      simp [s, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
        Matrix.map_apply, Matrix.one_apply, h, hc]
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, f.mapMatrix.map_mul, ha, hb]
  have hQ : Q (g : Matrix (Fin 4) (Fin 4) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      apply property_fin4_diagonal Q htrans hmul D
      exact hD.trans g.prop
    · exact htrans
    · exact hmul
  obtain ⟨a, ha⟩ := hQ
  refine ⟨a, Subtype.ext ?_⟩
  exact ha
noncomputable def indexSpecialLinearReduction
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) →*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  Matrix.SpecialLinearGroup.map (n := Fin r.matrixRank)
    (indexArithmeticEval P r level)
theorem indexSpecialLinearMap_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective
      (indexSpecialLinearReduction P r level) := by
  cases r with
  | three =>
      exact specialLinearMap_surjective_fin3
        (indexArithmeticEval P .three level)
        (indexArithmeticEval_surjective P .three level)
  | four =>
      exact specialLinearMap_surjective_fin4
        (indexArithmeticEval P .four level)
        (indexArithmeticEval_surjective P .four level)
noncomputable def IndexSpecialLinearCongruenceSubgroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P)) :=
  (indexSpecialLinearReduction P r level).ker
noncomputable instance indexSpecialLinearCongruenceSubgroupNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexSpecialLinearCongruenceSubgroup P r level).Normal := by
  dsimp [IndexSpecialLinearCongruenceSubgroup]
  infer_instance
noncomputable def indexSpecialLinearQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) ⧸
        IndexSpecialLinearCongruenceSubgroup P r level ≃*
      Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (indexSpecialLinearReduction P r level)
    (indexSpecialLinearMap_surjective P r level)
noncomputable def congruenceSpecialToProjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank) (ArithmeticRing P) →*
      PGL P r level :=
  (specialToProjective P r level).comp
    (indexSpecialLinearReduction P r level)
def rankFirstIndex (r : Rank) : Fin r.matrixRank :=
  ⟨0, by cases r <;> decide⟩
def rankSecondIndex (r : Rank) : Fin r.matrixRank :=
  ⟨1, by cases r <;> decide⟩
theorem rankFirstIndex_ne_rankSecondIndex (r : Rank) :
    rankFirstIndex r ≠ rankSecondIndex r := by
  cases r <;> decide
noncomputable def residueTransvectionSpecial
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ResidueField P r level) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  ⟨Matrix.transvection (rankFirstIndex r) (rankSecondIndex r) c,
    Matrix.det_transvection_of_ne
      (rankFirstIndex r) (rankSecondIndex r)
      (rankFirstIndex_ne_rankSecondIndex r) c⟩
noncomputable def residueTransvectionPSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ResidueField P r level) : PSL P r level :=
  ⟨specialToProjective P r level
      (residueTransvectionSpecial P r level c),
    ⟨residueTransvectionSpecial P r level c, rfl⟩⟩
end CongruenceLifting
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


