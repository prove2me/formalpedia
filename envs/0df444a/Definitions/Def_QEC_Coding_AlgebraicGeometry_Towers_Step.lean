-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
-- name    : QEC_Coding_AlgebraicGeometry_Towers_Step
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:44:24.044105+00:00
-- url     : https://prove2.me/theorems/d7e6b132-2554-4958-8386-653ffba66c9a
-- title:
--   Step
-- statement:
--   Definitions and structural lemmas for Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/Step.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
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
theorem coordinate_ne_zero (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : x ≠ 0 := by
  intro hzero
  subst x
  simp [GlobalPlace.order] at hx
noncomputable def reciprocalUniformizer (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : P.valuationRing :=
  ⟨x⁻¹, (P.regularAt_iff_mem_valuationRing x⁻¹).mp <|
    (P.regularAt_iff_order_nonnegative (inv_ne_zero (coordinate_ne_zero P x hx))).mpr <| by
      rw [P.order_inv, hx]
      norm_num⟩
@[simp]
theorem coe_reciprocalUniformizer (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    (reciprocalUniformizer P x hx : K) = x⁻¹ :=
  rfl
theorem reciprocalUniformizer_ne_zero (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : reciprocalUniformizer P x hx ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff]
  exact inv_ne_zero (coordinate_ne_zero P x hx)
theorem reciprocalUniformizer_order (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    P.order (reciprocalUniformizer P x hx : K) = 1 := by
  rw [coe_reciprocalUniformizer, P.order_inv, hx]
  norm_num
theorem valuation_reciprocalUniformizer (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    P.valuation (reciprocalUniformizer P x hx : K) = WithZero.exp (-1 : ℤ) := by
  have hne : P.valuation (reciprocalUniformizer P x hx : K) ≠ 0 :=
    P.valuation.ne_zero_iff.mpr (by
      simpa only [coe_reciprocalUniformizer] using
        inv_ne_zero (coordinate_ne_zero P x hx))
  have hlog : WithZero.log (P.valuation (reciprocalUniformizer P x hx : K)) = -1 := by
    have horder := reciprocalUniformizer_order P x hx
    simp only [GlobalPlace.order] at horder
    omega
  calc
    P.valuation (reciprocalUniformizer P x hx : K) =
        WithZero.exp (WithZero.log
          (P.valuation (reciprocalUniformizer P x hx : K))) :=
      (WithZero.exp_log hne).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]
theorem maximalIdeal_eq_span_reciprocalUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsLocalRing.maximalIdeal P.valuationRing =
      Ideal.span ({reciprocalUniformizer P x hx} : Set P.valuationRing) := by
  letI : P.valuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨P.uniformizer, ?_, ?_⟩
    · apply P.valuation.ne_zero_iff.mp
      rw [P.valuation_uniformizer]
      exact WithZero.exp_ne_zero
    · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : P.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' P.valuation
  apply Valuation.IsUniformizer.is_generator
  change P.valuation (reciprocalUniformizer P x hx : K) =
    ((Valuation.IsRankOneDiscrete.generator P.valuation :
      (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))
  rw [valuation_reciprocalUniformizer]
  simpa using congrArg
    (fun u : (WithZero (Multiplicative ℤ))ˣ =>
      (u : WithZero (Multiplicative ℤ)))
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := P.valuation) P.normalized).symm
theorem reciprocalUniformizer_mem_maximalIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    reciprocalUniformizer P x hx ∈ IsLocalRing.maximalIdeal P.valuationRing := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P x hx]
  exact Ideal.mem_span_singleton_self _
theorem reciprocalUniformizer_not_mem_maximalIdeal_sq
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    reciprocalUniformizer P x hx ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by
  rw [maximalIdeal_eq_span_reciprocalUniformizer P x hx,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have ht0 := reciprocalUniformizer_ne_zero P x hx
  have hone : (1 : P.valuationRing) = reciprocalUniformizer P x hx * c := by
    apply mul_left_cancel₀ ht0
    calc
      reciprocalUniformizer P x hx * 1 = reciprocalUniformizer P x hx :=
        mul_one _
      _ = reciprocalUniformizer P x hx ^ 2 * c := hc
      _ = reciprocalUniformizer P x hx *
          (reciprocalUniformizer P x hx * c) := by
        rw [pow_two, mul_assoc]
  have hunit : IsUnit (reciprocalUniformizer P x hx) :=
    isUnit_iff_exists_inv.mpr ⟨c, hone.symm⟩
  have hnotunit : ¬IsUnit (reciprocalUniformizer P x hx) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
      reciprocalUniformizer_mem_maximalIdeal P x hx
  exact hnotunit hunit
noncomputable def reciprocalPolynomial (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : P.valuationRing[X] :=
  X ^ 16 + C ((reciprocalUniformizer P x hx) ^ 16) * X ^ 15 +
    C (reciprocalUniformizer P x hx)
theorem reciprocalPolynomial_monic (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : (reciprocalPolynomial P x hx).Monic := by
  rw [reciprocalPolynomial, add_assoc]
  exact Monic.add_of_left (monic_X_pow 16) (by
    calc
      (C ((reciprocalUniformizer P x hx) ^ 16) * X ^ 15 +
          C (reciprocalUniformizer P x hx)).degree ≤ (15 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 15 _
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num)
@[simp]
theorem reciprocalPolynomial_natDegree (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : (reciprocalPolynomial P x hx).natDegree = 16 := by
  apply natDegree_eq_of_degree_eq_some
  rw [reciprocalPolynomial, add_assoc]
  rw [degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := P.valuationRing) 16
  · calc
      (C ((reciprocalUniformizer P x hx) ^ 16) * X ^ 15 +
          C (reciprocalUniformizer P x hx)).degree ≤ (15 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 15 _
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num
theorem reciprocalPolynomial_isEisenstein
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (reciprocalPolynomial P x hx).IsEisensteinAt
      (IsLocalRing.maximalIdeal P.valuationRing) := by
  apply (reciprocalPolynomial_monic P x hx).isEisensteinAt_of_mem_of_notMem
  · exact (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).ne_top
  · intro n hn
    rw [reciprocalPolynomial_natDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff : (reciprocalPolynomial P x hx).coeff 0 =
          reciprocalUniformizer P x hx := by
        simp only [reciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C_zero]
        norm_num
      rw [hcoeff]
      exact reciprocalUniformizer_mem_maximalIdeal P x hx
    by_cases hn15 : n = 15
    · subst n
      have ht := reciprocalUniformizer_mem_maximalIdeal P x hx
      have hcoeff : (reciprocalPolynomial P x hx).coeff 15 =
          reciprocalUniformizer P x hx ^ 16 := by
        simp only [reciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C]
        norm_num
      rw [hcoeff]
      exact (IsLocalRing.maximalIdeal P.valuationRing).pow_mem_of_mem ht 16
        (by norm_num)
    · have hn16 : n ≠ 16 := by omega
      have hcoeff : (reciprocalPolynomial P x hx).coeff n = 0 := by
        simp only [reciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C, if_neg hn16,
          if_neg hn15, if_neg hn0, zero_add]
      rw [hcoeff]
      exact Ideal.zero_mem _
  · have hcoeff : (reciprocalPolynomial P x hx).coeff 0 =
        reciprocalUniformizer P x hx := by
      simp only [reciprocalPolynomial, coeff_add, coeff_X_pow,
        Polynomial.coeff_C_mul_X_pow, coeff_C_zero]
      norm_num
    rw [hcoeff]
    exact reciprocalUniformizer_not_mem_maximalIdeal_sq P x hx
noncomputable def stepPolynomial (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : K[X] :=
  (reciprocalPolynomial P x hx).map (algebraMap P.valuationRing K)
theorem stepPolynomial_eq_explicit (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    stepPolynomial P x hx = X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹ := by
  simp [stepPolynomial, reciprocalPolynomial, coe_reciprocalUniformizer]
  rw [← map_pow, inv_pow]
theorem stepPolynomial_monic (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : (stepPolynomial P x hx).Monic :=
  (reciprocalPolynomial_monic P x hx).map _
@[simp]
theorem stepPolynomial_natDegree (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : (stepPolynomial P x hx).natDegree = 16 := by
  rw [stepPolynomial, (reciprocalPolynomial_monic P x hx).natDegree_map,
    reciprocalPolynomial_natDegree]
theorem stepPolynomial_irreducible (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : Irreducible (stepPolynomial P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  have hirr : Irreducible (reciprocalPolynomial P x hx) :=
    (reciprocalPolynomial_isEisenstein P x hx).irreducible
      (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).isPrime
      (reciprocalPolynomial_monic P x hx).isPrimitive
      (by rw [reciprocalPolynomial_natDegree]; norm_num)
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := K) (reciprocalPolynomial_monic P x hx)).mp hirr
theorem stepPolynomial_separable (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : (stepPolynomial P x hx).Separable := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  rw [Polynomial.separable_iff_derivative_ne_zero
    (stepPolynomial_irreducible P x hx)]
  have hderivative : (stepPolynomial P x hx).derivative =
      C (x⁻¹ ^ 16) * X ^ 14 := by
    rw [stepPolynomial_eq_explicit]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X_pow, derivative_C]
    reduce_mod_char!
    norm_num [inv_pow]
  rw [hderivative]
  exact mul_ne_zero
    (C_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero (coordinate_ne_zero P x hx))))
    (pow_ne_zero _ X_ne_zero)
abbrev StepField (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  AdjoinRoot (stepPolynomial P x hx)
noncomputable instance stepPolynomialIrreducibleFact
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Fact (Irreducible (stepPolynomial P x hx)) :=
  ⟨stepPolynomial_irreducible P x hx⟩
noncomputable def stepFieldEmbedding (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : K →ₐ[K] StepField P x hx :=
  Algebra.ofId K (StepField P x hx)
noncomputable def stepReciprocalRoot (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : StepField P x hx :=
  AdjoinRoot.root (stepPolynomial P x hx)
noncomputable def stepAuxiliaryCoordinate (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) : StepField P x hx :=
  stepFieldEmbedding P x hx x / stepReciprocalRoot P x hx
noncomputable def stepDistinguishedCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    StepField P x hx :=
  stepAuxiliaryCoordinate P x hx / stepFieldEmbedding P x hx x
noncomputable instance stepField_isSeparable
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Algebra.IsSeparable K (StepField P x hx) := by
  let w := stepReciprocalRoot P x hx
  have hwsep : IsSeparable K w := by
    dsimp [w, stepReciprocalRoot]
    rw [IsSeparable, AdjoinRoot.minpoly_root
      (stepPolynomial_monic P x hx).ne_zero,
      (stepPolynomial_monic P x hx).leadingCoeff, inv_one, C.map_one,
      mul_one]
    exact stepPolynomial_separable P x hx
  letI : Algebra.IsSeparable K
      (IntermediateField.adjoin K ({w} : Set (StepField P x hx))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := StepField P x hx) (x := w)).mpr hwsep
  have hAlgebraAdjoin : Algebra.adjoin K
      ({w} : Set (StepField P x hx)) = ⊤ := by
    exact (AdjoinRoot.powerBasis
      (stepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
  have hadjoin : IntermediateField.adjoin K
      ({w} : Set (StepField P x hx)) = ⊤ := by
    apply top_unique
    intro y _
    exact (IntermediateField.algebra_adjoin_le_adjoin K
      ({w} : Set (StepField P x hx))) (by
        rw [hAlgebraAdjoin]
        exact Set.mem_univ y)
  refine ⟨fun y => IntermediateField.isSeparable_of_mem_isSeparable
    (F := K) (E := StepField P x hx)
    (L := IntermediateField.adjoin K ({w} : Set (StepField P x hx))) ?_⟩
  rw [hadjoin]
  exact Set.mem_univ y
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


