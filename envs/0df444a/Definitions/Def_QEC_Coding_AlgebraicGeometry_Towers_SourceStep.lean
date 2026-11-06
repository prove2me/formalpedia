-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:45:00.042719+00:00
-- url     : https://prove2.me/theorems/76b7a0d7-677d-4af5-b2c8-255c2d1f1d36
-- title:
--   Source Step
-- statement:
--   Definitions and structural lemmas for Source Step, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceStep.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
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
def sourceStepRhs (x : K) : K :=
  x ^ 16 / (x ^ 15 + 1)
theorem sourceStep_coordinate_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) : x ≠ 0 := by
  intro hzero
  subst x
  simp [GlobalPlace.order] at hx
theorem sourceStep_order_pow
    (P : GlobalPlace F256 K) (x : K) (n : ℕ) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring
theorem sourceStep_valuation_eq_exp_neg_order
    (P : GlobalPlace F256 K) (y : K) (hy : y ≠ 0) :
    P.valuation y = WithZero.exp (-P.order y) := by
  unfold GlobalPlace.order
  rw [neg_neg]
  exact (WithZero.exp_log (P.valuation.ne_zero_iff.mpr hy)).symm
theorem sourceStep_denominator_order
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.order (x ^ 15 + 1) = -15 := by
  have hx_ne := sourceStep_coordinate_ne_zero P x hx
  have hxpow_ne : x ^ 15 ≠ 0 := pow_ne_zero 15 hx_ne
  have hxpow_order : P.order (x ^ 15) = -15 := by
    rw [sourceStep_order_pow, hx]
    norm_num
  have hxpow_value : P.valuation (x ^ 15) = WithZero.exp (15 : ℤ) := by
    rw [sourceStep_valuation_eq_exp_neg_order P (x ^ 15) hxpow_ne,
      hxpow_order]
    norm_num
  have hlt : P.valuation 1 < P.valuation (x ^ 15) := by
    rw [map_one, hxpow_value, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  unfold GlobalPlace.order
  rw [P.valuation.map_add_eq_of_lt_left hlt, hxpow_value,
    WithZero.log_exp]
theorem sourceStep_denominator_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    x ^ 15 + 1 ≠ 0 := by
  intro hzero
  have horder := sourceStep_denominator_order P x hx
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder
theorem sourceStepRhs_order
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.order (sourceStepRhs x) = -1 := by
  have hx_ne := sourceStep_coordinate_ne_zero P x hx
  have hden_ne := sourceStep_denominator_ne_zero P x hx
  rw [sourceStepRhs, div_eq_mul_inv,
    P.order_mul (pow_ne_zero 16 hx_ne) (inv_ne_zero hden_ne),
    P.order_inv, sourceStep_order_pow, hx,
    sourceStep_denominator_order P x hx]
  norm_num
theorem sourceStepRhs_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepRhs x ≠ 0 := by
  rw [sourceStepRhs]
  exact div_ne_zero (pow_ne_zero 16 (sourceStep_coordinate_ne_zero P x hx))
    (sourceStep_denominator_ne_zero P x hx)
noncomputable def sourceStepUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.valuationRing :=
  reciprocalUniformizer P (sourceStepRhs x) (sourceStepRhs_order P x hx)
@[simp]
theorem coe_sourceStepUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepUniformizer P x hx : K) = (sourceStepRhs x)⁻¹ :=
  rfl
theorem sourceStepUniformizer_ne_zero
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepUniformizer P x hx ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff]
  exact inv_ne_zero (sourceStepRhs_ne_zero P x hx)
noncomputable def sourceStepReciprocalPolynomial
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    P.valuationRing[X] :=
  X ^ 16 + C (sourceStepUniformizer P x hx) * X ^ 15 +
    C (sourceStepUniformizer P x hx)
theorem sourceStepReciprocalPolynomial_monic
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepReciprocalPolynomial P x hx).Monic := by
  rw [sourceStepReciprocalPolynomial, add_assoc]
  exact Monic.add_of_left (monic_X_pow 16) (by
    calc
      (C (sourceStepUniformizer P x hx) * X ^ 15 +
          C (sourceStepUniformizer P x hx)).degree ≤ (15 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 15 _
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num)
@[simp]
theorem sourceStepReciprocalPolynomial_natDegree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepReciprocalPolynomial P x hx).natDegree = 16 := by
  apply natDegree_eq_of_degree_eq_some
  rw [sourceStepReciprocalPolynomial, add_assoc,
    degree_add_eq_left_of_degree_lt]
  · exact degree_X_pow (R := P.valuationRing) 16
  · calc
      (C (sourceStepUniformizer P x hx) * X ^ 15 +
          C (sourceStepUniformizer P x hx)).degree ≤ (15 : WithBot ℕ) := by
        apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 15 _
        · exact degree_C_le.trans (by norm_num)
      _ < ((X : P.valuationRing[X]) ^ 16).degree := by
        rw [degree_X_pow]
        norm_num
theorem sourceStepReciprocalPolynomial_isEisenstein
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepReciprocalPolynomial P x hx).IsEisensteinAt
      (IsLocalRing.maximalIdeal P.valuationRing) := by
  have ht_mem : sourceStepUniformizer P x hx ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx)]
    exact Ideal.mem_span_singleton_self _
  have ht_not_sq : sourceStepUniformizer P x hx ∉
      (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx),
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have ht0 := sourceStepUniformizer_ne_zero P x hx
    have hone : (1 : P.valuationRing) = sourceStepUniformizer P x hx * c := by
      apply mul_left_cancel₀ ht0
      calc
        sourceStepUniformizer P x hx * 1 = sourceStepUniformizer P x hx := mul_one _
        _ = sourceStepUniformizer P x hx ^ 2 * c := hc
        _ = sourceStepUniformizer P x hx *
            (sourceStepUniformizer P x hx * c) := by rw [pow_two, mul_assoc]
    have hunit : IsUnit (sourceStepUniformizer P x hx) :=
      isUnit_iff_exists_inv.mpr ⟨c, hone.symm⟩
    have hnotunit : ¬IsUnit (sourceStepUniformizer P x hx) := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ht_mem
    exact hnotunit hunit
  apply (sourceStepReciprocalPolynomial_monic P x hx).isEisensteinAt_of_mem_of_notMem
  · exact (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).ne_top
  · intro n hn
    rw [sourceStepReciprocalPolynomial_natDegree] at hn
    by_cases hn0 : n = 0
    · subst n
      have hcoeff : (sourceStepReciprocalPolynomial P x hx).coeff 0 =
          sourceStepUniformizer P x hx := by
        simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C_zero]
        norm_num
      rw [hcoeff]
      exact ht_mem
    by_cases hn15 : n = 15
    · subst n
      have hcoeff : (sourceStepReciprocalPolynomial P x hx).coeff 15 =
          sourceStepUniformizer P x hx := by
        simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C]
        norm_num
      rw [hcoeff]
      exact ht_mem
    · have hn16 : n ≠ 16 := by omega
      simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
        Polynomial.coeff_C_mul_X_pow, coeff_C, if_neg hn16,
        if_neg hn15, if_neg hn0, zero_add, Ideal.zero_mem]
  · have hcoeff : (sourceStepReciprocalPolynomial P x hx).coeff 0 =
        sourceStepUniformizer P x hx := by
      simp only [sourceStepReciprocalPolynomial, coeff_add, coeff_X_pow,
        Polynomial.coeff_C_mul_X_pow, coeff_C_zero]
      norm_num
    rw [hcoeff]
    exact ht_not_sq
noncomputable def sourceStepPolynomial
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) : K[X] :=
  (sourceStepReciprocalPolynomial P x hx).map
    (algebraMap P.valuationRing K)
theorem sourceStepPolynomial_eq_explicit
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepPolynomial P x hx =
      X ^ 16 + C (sourceStepRhs x)⁻¹ * X ^ 15 + C (sourceStepRhs x)⁻¹ := by
  simp [sourceStepPolynomial, sourceStepReciprocalPolynomial,
    sourceStepUniformizer, coe_reciprocalUniformizer]
theorem sourceStepPolynomial_monic
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepPolynomial P x hx).Monic :=
  (sourceStepReciprocalPolynomial_monic P x hx).map _
@[simp]
theorem sourceStepPolynomial_natDegree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepPolynomial P x hx).natDegree = 16 := by
  rw [sourceStepPolynomial,
    (sourceStepReciprocalPolynomial_monic P x hx).natDegree_map,
    sourceStepReciprocalPolynomial_natDegree]
theorem sourceStepPolynomial_irreducible
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Irreducible (sourceStepPolynomial P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  have hirr : Irreducible (sourceStepReciprocalPolynomial P x hx) :=
    (sourceStepReciprocalPolynomial_isEisenstein P x hx).irreducible
      (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).isPrime
      (sourceStepReciprocalPolynomial_monic P x hx).isPrimitive
      (by rw [sourceStepReciprocalPolynomial_natDegree]; norm_num)
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := K) (sourceStepReciprocalPolynomial_monic P x hx)).mp hirr
theorem sourceStepPolynomial_separable
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepPolynomial P x hx).Separable := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  rw [Polynomial.separable_iff_derivative_ne_zero
    (sourceStepPolynomial_irreducible P x hx)]
  have hderivative : (sourceStepPolynomial P x hx).derivative =
      C (sourceStepRhs x)⁻¹ * X ^ 14 := by
    rw [sourceStepPolynomial_eq_explicit]
    simp only [derivative_add, derivative_X_pow,
      derivative_C_mul_X_pow, derivative_C]
    reduce_mod_char!
    norm_num
  rw [hderivative]
  exact mul_ne_zero
    (C_ne_zero.mpr (inv_ne_zero (sourceStepRhs_ne_zero P x hx)))
    (pow_ne_zero _ X_ne_zero)
abbrev SourceStepField
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :=
  AdjoinRoot (sourceStepPolynomial P x hx)
noncomputable instance sourceStepPolynomialIrreducibleFact
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Fact (Irreducible (sourceStepPolynomial P x hx)) :=
  ⟨sourceStepPolynomial_irreducible P x hx⟩
noncomputable instance sourceStepConstantScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower F256 K (SourceStepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def sourceStepEmbedding
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    K →ₐ[F256] SourceStepField P x hx :=
  (Algebra.ofId K (SourceStepField P x hx)).restrictScalars F256
noncomputable def sourceStepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepField P x hx :=
  AdjoinRoot.root (sourceStepPolynomial P x hx)
noncomputable def sourceStepCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepField P x hx :=
  (sourceStepReciprocalRoot P x hx)⁻¹
noncomputable instance sourceStepFiniteDimensional
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    FiniteDimensional K (SourceStepField P x hx) :=
  (AdjoinRoot.powerBasis (sourceStepPolynomial_monic P x hx).ne_zero).finite
noncomputable instance sourceStep_isSeparable
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Algebra.IsSeparable K (SourceStepField P x hx) := by
  let w := sourceStepReciprocalRoot P x hx
  have hwsep : IsSeparable K w := by
    dsimp [w, sourceStepReciprocalRoot]
    rw [IsSeparable, AdjoinRoot.minpoly_root
      (sourceStepPolynomial_monic P x hx).ne_zero,
      (sourceStepPolynomial_monic P x hx).leadingCoeff, inv_one, C.map_one,
      mul_one]
    exact sourceStepPolynomial_separable P x hx
  letI : Algebra.IsSeparable K
      (IntermediateField.adjoin K ({w} : Set (SourceStepField P x hx))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := SourceStepField P x hx) (x := w)).mpr hwsep
  have hAlgebraAdjoin : Algebra.adjoin K
      ({w} : Set (SourceStepField P x hx)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (sourceStepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
    simp only [w, sourceStepReciprocalRoot] at hport ⊢
    exact hport
  have hadjoin : IntermediateField.adjoin K
      ({w} : Set (SourceStepField P x hx)) = ⊤ := by
    apply top_unique
    intro y _
    exact (IntermediateField.algebra_adjoin_le_adjoin K
      ({w} : Set (SourceStepField P x hx))) (by
        rw [hAlgebraAdjoin]
        exact Set.mem_univ y)
  refine ⟨fun y => IntermediateField.isSeparable_of_mem_isSeparable
    (F := K) (E := SourceStepField P x hx)
    (L := IntermediateField.adjoin K ({w} : Set (SourceStepField P x hx))) ?_⟩
  rw [hadjoin]
  exact Set.mem_univ y
instance sourceStepValuationRingScalarTower
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsScalarTower P.valuationRing K (SourceStepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl
abbrev SourceStepIntegralClosure
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :=
  integralClosure P.valuationRing (SourceStepField P x hx)
noncomputable instance sourceStepIntegralClosureIsTorsionFree
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.IsTorsionFree P.valuationRing
      (SourceStepIntegralClosure P x hx) := by
  letI : Module.IsTorsionFree P.valuationRing (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (SourceStepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    P.valuationRing (SourceStepField P x hx)
noncomputable instance sourceStepIntegralClosureFinite
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Module.Finite P.valuationRing (SourceStepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite P.valuationRing K (SourceStepField P x hx)
    (SourceStepIntegralClosure P x hx)
noncomputable instance sourceStepIntegralClosureIsFractionRing
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsFractionRing (SourceStepIntegralClosure P x hx)
      (SourceStepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K
    (SourceStepField P x hx)
noncomputable instance sourceStepIntegralClosureIsDedekindDomain
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain (SourceStepIntegralClosure P x hx) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain P.valuationRing K
    (SourceStepField P x hx)
noncomputable def sourceStepIntegralRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepIntegralClosure P x hx := by
  refine ⟨sourceStepReciprocalRoot P x hx, ?_⟩
  refine ⟨sourceStepReciprocalPolynomial P x hx,
    sourceStepReciprocalPolynomial_monic P x hx, ?_⟩
  change eval₂
      ((AdjoinRoot.of (sourceStepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (sourceStepReciprocalRoot P x hx)
      (sourceStepReciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)
noncomputable def sourceStepIntegralUniformizer
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    SourceStepIntegralClosure P x hx := by
  refine ⟨sourceStepEmbedding P x hx (sourceStepRhs x)⁻¹, ?_⟩
  change IsIntegral P.valuationRing
    (algebraMap P.valuationRing (SourceStepField P x hx)
      (sourceStepUniformizer P x hx))
  exact isIntegral_algebraMap
theorem exists_sourceStepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    ∃ Q : Ideal (SourceStepIntegralClosure P x hx),
      Q.IsMaximal ∧ Q.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := SourceStepIntegralClosure P x hx)
    (IsLocalRing.maximalIdeal P.valuationRing)
noncomputable def sourceStepUpperIdeal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Ideal (SourceStepIntegralClosure P x hx) :=
  Classical.choose (exists_sourceStepUpperIdeal P x hx)
theorem sourceStepUpperIdeal_isMaximal
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepUpperIdeal P x hx).IsMaximal :=
  (Classical.choose_spec (exists_sourceStepUpperIdeal P x hx)).1
theorem sourceStepUpperIdeal_liesOver
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
  (Classical.choose_spec (exists_sourceStepUpperIdeal P x hx)).2
noncomputable def sourceStepUpperHeightOne
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IsDedekindDomain.HeightOneSpectrum (SourceStepIntegralClosure P x hx) :=
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : (sourceStepUpperIdeal P x hx).LiesOver
      (IsLocalRing.maximalIdeal P.valuationRing) :=
    sourceStepUpperIdeal_liesOver P x hx
  { asIdeal := sourceStepUpperIdeal P x hx
    isPrime := (sourceStepUpperIdeal_isMaximal P x hx).isPrime
    ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field P.valuationRing)
      (sourceStepUpperIdeal P x hx) }
noncomputable def sourceStepAbovePlace
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    GlobalPlace F256 (SourceStepField P x hx) where
  valuation := (sourceStepUpperHeightOne P x hx).valuation
    (SourceStepField P x hx)
  normalized := (sourceStepUpperHeightOne P x hx).valuation_surjective
    (SourceStepField P x hx)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


