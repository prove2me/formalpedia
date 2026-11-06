-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
-- name    : QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:45:01.318127+00:00
-- url     : https://prove2.me/theorems/d637da16-3665-4e0d-bd8d-9aa9df3fa081
-- title:
--   Quadratic Step
-- statement:
--   Definitions and structural lemmas for Quadratic Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticStep.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem quadraticArtinSchreier_parameter_ne_zero
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) : a ≠ 0 := by
  intro hzero
  subst a
  simp [GlobalPlace.order] at ha
theorem quadraticArtinSchreier_uniformizer_ne_zero
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    reciprocalUniformizer P a ha ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff]
  exact inv_ne_zero (quadraticArtinSchreier_parameter_ne_zero P a ha)
theorem quadraticArtinSchreier_uniformizer_mem_maximalIdeal
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    reciprocalUniformizer P a ha ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha]
  exact Ideal.mem_span_singleton_self _
theorem quadraticArtinSchreier_uniformizer_not_mem_maximalIdeal_sq
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    reciprocalUniformizer P a ha ∉
      (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have ht0 := quadraticArtinSchreier_uniformizer_ne_zero P a ha
  have hone : (1 : P.valuationRing) = reciprocalUniformizer P a ha * c := by
    apply mul_left_cancel₀ ht0
    calc
      reciprocalUniformizer P a ha * 1 = reciprocalUniformizer P a ha :=
        mul_one _
      _ = reciprocalUniformizer P a ha ^ 2 * c := hc
      _ = reciprocalUniformizer P a ha *
          (reciprocalUniformizer P a ha * c) := by
        rw [pow_two, mul_assoc]
  have hunit : IsUnit (reciprocalUniformizer P a ha) :=
    isUnit_iff_exists_inv.mpr ⟨c, hone.symm⟩
  have hnotunit : ¬IsUnit (reciprocalUniformizer P a ha) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
      quadraticArtinSchreier_uniformizer_mem_maximalIdeal P a ha
  exact hnotunit hunit
noncomputable def quadraticArtinSchreierReciprocalPolynomial
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    P.valuationRing[X] :=
  X ^ 2 + C (reciprocalUniformizer P a ha) * X +
    C (reciprocalUniformizer P a ha)
theorem quadraticArtinSchreierReciprocalPolynomial_monic
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierReciprocalPolynomial P a ha).Monic := by
  rw [quadraticArtinSchreierReciprocalPolynomial, add_assoc]
  exact Monic.add_of_left (monic_X_pow 2) (by
    calc
      (C (reciprocalUniformizer P a ha) * X +
          C (reciprocalUniformizer P a ha)).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · have hdegree := degree_C_mul_X_pow_le 1 (reciprocalUniformizer P a ha)
          simp only [pow_one] at hdegree
          exact hdegree
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 2).degree := by
        rw [degree_X_pow]
        norm_num)
@[simp]
theorem quadraticArtinSchreierReciprocalPolynomial_natDegree
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierReciprocalPolynomial P a ha).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  rw [quadraticArtinSchreierReciprocalPolynomial, add_assoc,
    degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := P.valuationRing) 2
  · calc
      (C (reciprocalUniformizer P a ha) * X +
          C (reciprocalUniformizer P a ha)).degree ≤ (1 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · have hdegree := degree_C_mul_X_pow_le 1 (reciprocalUniformizer P a ha)
          simp only [pow_one] at hdegree
          exact hdegree
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 2).degree := by
        rw [degree_X_pow]
        norm_num
theorem quadraticArtinSchreierReciprocalPolynomial_isEisenstein
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierReciprocalPolynomial P a ha).IsEisensteinAt
      (IsLocalRing.maximalIdeal P.valuationRing) := by
  apply
    (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).isEisensteinAt_of_mem_of_notMem
  · exact (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).ne_top
  · intro n hn
    rw [quadraticArtinSchreierReciprocalPolynomial_natDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff :
          (quadraticArtinSchreierReciprocalPolynomial P a ha).coeff 0 =
            reciprocalUniformizer P a ha := by
        simp only [quadraticArtinSchreierReciprocalPolynomial, coeff_add,
          coeff_X_pow, Polynomial.coeff_C_mul_X, coeff_C_zero]
        norm_num
      rw [hcoeff]
      exact quadraticArtinSchreier_uniformizer_mem_maximalIdeal P a ha
    by_cases hn1 : n = 1
    · subst n
      have hcoeff :
          (quadraticArtinSchreierReciprocalPolynomial P a ha).coeff 1 =
            reciprocalUniformizer P a ha := by
        simp only [quadraticArtinSchreierReciprocalPolynomial, coeff_add,
          coeff_X_pow, Polynomial.coeff_C_mul_X, coeff_C]
        norm_num
      rw [hcoeff]
      exact quadraticArtinSchreier_uniformizer_mem_maximalIdeal P a ha
    · omega
  · have hcoeff :
        (quadraticArtinSchreierReciprocalPolynomial P a ha).coeff 0 =
          reciprocalUniformizer P a ha := by
      simp only [quadraticArtinSchreierReciprocalPolynomial, coeff_add,
        coeff_X_pow, Polynomial.coeff_C_mul_X, coeff_C_zero]
      norm_num
    rw [hcoeff]
    exact quadraticArtinSchreier_uniformizer_not_mem_maximalIdeal_sq P a ha
noncomputable def quadraticArtinSchreierPolynomial
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) : K[X] :=
  (quadraticArtinSchreierReciprocalPolynomial P a ha).map
    (algebraMap P.valuationRing K)
theorem quadraticArtinSchreierPolynomial_eq_explicit
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierPolynomial P a ha =
      X ^ 2 + C a⁻¹ * X + C a⁻¹ := by
  simp [quadraticArtinSchreierPolynomial,
    quadraticArtinSchreierReciprocalPolynomial,
    coe_reciprocalUniformizer]
theorem quadraticArtinSchreierPolynomial_monic
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierPolynomial P a ha).Monic :=
  (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).map _
@[simp]
theorem quadraticArtinSchreierPolynomial_natDegree
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierPolynomial P a ha).natDegree = 2 := by
  rw [quadraticArtinSchreierPolynomial,
    (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).natDegree_map,
    quadraticArtinSchreierReciprocalPolynomial_natDegree]
theorem quadraticArtinSchreierPolynomial_irreducible
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Irreducible (quadraticArtinSchreierPolynomial P a ha) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  have hirr :
      Irreducible (quadraticArtinSchreierReciprocalPolynomial P a ha) :=
    (quadraticArtinSchreierReciprocalPolynomial_isEisenstein P a ha).irreducible
      (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).isPrime
      (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).isPrimitive
      (by
        rw [quadraticArtinSchreierReciprocalPolynomial_natDegree]
        norm_num)
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := K) (quadraticArtinSchreierReciprocalPolynomial_monic P a ha)).mp hirr
theorem quadraticArtinSchreierPolynomial_separable
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierPolynomial P a ha).Separable := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  rw [Polynomial.separable_iff_derivative_ne_zero
    (quadraticArtinSchreierPolynomial_irreducible P a ha)]
  have hderivative :
      (quadraticArtinSchreierPolynomial P a ha).derivative = C a⁻¹ := by
    rw [quadraticArtinSchreierPolynomial_eq_explicit]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  exact C_ne_zero.mpr
    (inv_ne_zero (quadraticArtinSchreier_parameter_ne_zero P a ha))
abbrev QuadraticArtinSchreierField
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :=
  AdjoinRoot (quadraticArtinSchreierPolynomial P a ha)
noncomputable instance quadraticArtinSchreierPolynomialIrreducibleFact
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Fact (Irreducible (quadraticArtinSchreierPolynomial P a ha)) :=
  ⟨quadraticArtinSchreierPolynomial_irreducible P a ha⟩
noncomputable instance quadraticArtinSchreierConstantScalarTower
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    IsScalarTower F256 K (QuadraticArtinSchreierField P a ha) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def quadraticArtinSchreierEmbedding
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    K →ₐ[F256] QuadraticArtinSchreierField P a ha :=
  (Algebra.ofId K (QuadraticArtinSchreierField P a ha)).restrictScalars F256
noncomputable def quadraticArtinSchreierReciprocalRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierField P a ha :=
  AdjoinRoot.root (quadraticArtinSchreierPolynomial P a ha)
noncomputable def quadraticArtinSchreierCoordinate
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    QuadraticArtinSchreierField P a ha :=
  (quadraticArtinSchreierReciprocalRoot P a ha)⁻¹
noncomputable instance quadraticArtinSchreierFiniteDimensional
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    FiniteDimensional K (QuadraticArtinSchreierField P a ha) :=
  (AdjoinRoot.powerBasis
    (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero).finite
noncomputable instance quadraticArtinSchreier_isSeparable
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Algebra.IsSeparable K (QuadraticArtinSchreierField P a ha) := by
  let w := quadraticArtinSchreierReciprocalRoot P a ha
  have hwsep : IsSeparable K w := by
    dsimp [w, quadraticArtinSchreierReciprocalRoot]
    rw [IsSeparable, AdjoinRoot.minpoly_root
      (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero,
      (quadraticArtinSchreierPolynomial_monic P a ha).leadingCoeff,
      inv_one, C.map_one, mul_one]
    exact quadraticArtinSchreierPolynomial_separable P a ha
  letI : Algebra.IsSeparable K
      (IntermediateField.adjoin K
        ({w} : Set (QuadraticArtinSchreierField P a ha))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := QuadraticArtinSchreierField P a ha) (x := w)).mpr hwsep
  have hAlgebraAdjoin : Algebra.adjoin K
      ({w} : Set (QuadraticArtinSchreierField P a ha)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero).adjoin_gen_eq_top
    simp only [w, quadraticArtinSchreierReciprocalRoot] at hport ⊢
    exact hport
  have hadjoin : IntermediateField.adjoin K
      ({w} : Set (QuadraticArtinSchreierField P a ha)) = ⊤ := by
    apply top_unique
    intro y _
    exact (IntermediateField.algebra_adjoin_le_adjoin K
      ({w} : Set (QuadraticArtinSchreierField P a ha))) (by
        rw [hAlgebraAdjoin]
        exact Set.mem_univ y)
  refine ⟨fun y => IntermediateField.isSeparable_of_mem_isSeparable
    (F := K) (E := QuadraticArtinSchreierField P a ha)
    (L := IntermediateField.adjoin K
      ({w} : Set (QuadraticArtinSchreierField P a ha))) ?_⟩
  rw [hadjoin]
  exact Set.mem_univ y
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


