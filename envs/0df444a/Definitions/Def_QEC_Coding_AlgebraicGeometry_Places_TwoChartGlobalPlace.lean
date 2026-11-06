-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
-- name    : QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:16:29.303479+00:00
-- url     : https://prove2.me/theorems/2db11dc3-fd43-43a5-8cd0-708984a239de
-- title:
--   Two Chart Global Place
-- statement:
--   Definitions and structural lemmas for Two Chart Global Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/TwoChartGlobalPlace.lean

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_coordinate_valuation_lt_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
theorem rankOneDiscrete_of_surjective
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.IsRankOneDiscrete := by
  let γ : ℤᵐ⁰ˣ := Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp)
  refine ⟨γ, ?_, ?_⟩
  · apply Subgroup.ext
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hv x.1
      have ha0 : v a ≠ 0 := by simpa only [ha] using x.ne_zero
      have hunit : Units.mk0 (v a) ha0 = x := Units.ext ha
      rw [← hunit]
      exact MonoidWithZeroHom.mem_valueGroup (MonoidWithZeroHom.ofClass v)
        (show (Units.mk0 (v a) ha0 : ℤᵐ⁰ˣ).1 ∈ Set.range v from ⟨a, rfl⟩)
    · intro hx
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-WithZero.log x.1, ?_⟩
      apply Units.ext
      rw [Units.val_zpow_eq_zpow_val]
      change (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ (-WithZero.log x.1) = x.1
      rw [← WithZero.exp_zsmul]
      simpa only [Int.zsmul_eq_mul, neg_mul_neg, one_mul, mul_one] using
        (WithZero.exp_log x.ne_zero)
  · change (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1
    simpa using (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by decide))
noncomputable def normalizedValueGroupOrderIso
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] : ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰ :=
  Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
noncomputable def normalizedCodomainOrderAuto
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) : ℤᵐ⁰ ≃*o ℤᵐ⁰ :=
  (normalizedValueGroupOrderIso v).symm.trans
    ((h.orderMonoidIso).trans (normalizedValueGroupOrderIso w))
noncomputable def normalizedUnitOrderAuto
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : Multiplicative ℤ ≃*o Multiplicative ℤ :=
  OrderMonoidIso.withZero.symm φ
noncomputable def normalizedIntOrderAuto
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : ℤ ≃+o ℤ :=
  (OrderMonoidIso.toAdditiveRight (normalizedUnitOrderAuto φ)).trans
    (OrderAddMonoidIso.toAdditive_toMultiplicative (G := ℤ))
theorem normalizedCodomainOrderAuto_eq_id
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : φ = OrderMonoidIso.refl ℤᵐ⁰ := by
  have hunit : normalizedUnitOrderAuto φ = OrderMonoidIso.refl (Multiplicative ℤ) :=
    Subsingleton.elim _ _
  calc
    φ = OrderMonoidIso.withZero (normalizedUnitOrderAuto φ) :=
      (OrderMonoidIso.withZero.apply_symm_apply φ).symm
    _ = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) :=
      congrArg OrderMonoidIso.withZero hunit
    _ = OrderMonoidIso.refl ℤᵐ⁰ := by
      apply OrderMonoidIso.toMulEquiv_injective
      apply MulEquiv.ext
      intro x
      cases x <;> rfl
theorem normalizedCodomainOrderAuto_apply_restrict
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) (a : F) :
    normalizedCodomainOrderAuto v w h
        (normalizedValueGroupOrderIso v (v.restrict a)) =
      normalizedValueGroupOrderIso w (w.restrict a) := by
  change normalizedValueGroupOrderIso w
      (h.orderMonoidIso
        ((normalizedValueGroupOrderIso v).symm
          (normalizedValueGroupOrderIso v (v.restrict a)))) =
    normalizedValueGroupOrderIso w (w.restrict a)
  rw [(normalizedValueGroupOrderIso v).symm_apply_apply]
  rw [h.orderMonoidIso_spec]
theorem normalizedCodomainOrderAuto_value_eq
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w)
    (hφ : normalizedCodomainOrderAuto v w h = OrderMonoidIso.refl ℤᵐ⁰)
    (a : F) : v a = w a := by
  calc
    v a = normalizedValueGroupOrderIso v (v.restrict a) :=
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (v := v) hv a).symm
    _ = normalizedCodomainOrderAuto v w h
          (normalizedValueGroupOrderIso v (v.restrict a)) := by
      rw [hφ]
      rfl
    _ = normalizedValueGroupOrderIso w (w.restrict a) :=
      normalizedCodomainOrderAuto_apply_restrict v w h a
    _ = w a :=
      Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (v := w) hw a
theorem valuation_eq_of_surjective_isEquiv_withZeroMulInt
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w := by
  letI : v.IsRankOneDiscrete := rankOneDiscrete_of_surjective v hv
  letI : w.IsRankOneDiscrete := rankOneDiscrete_of_surjective w hw
  let φ := normalizedCodomainOrderAuto v w h
  have hφ : φ = OrderMonoidIso.refl ℤᵐ⁰ := normalizedCodomainOrderAuto_eq_id φ
  apply Valuation.ext
  intro a
  exact normalizedCodomainOrderAuto_value_eq v w hv hw h hφ a
theorem polynomial_map_mem_valuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    (ι : k[X] →+* F) (v : Valuation F ℤᵐ⁰)
    (hX : v (ι Polynomial.X) ≤ 1) (p : k[X]) :
    ι p ∈ v.valuationSubring := by
  letI : Algebra k F := (ι.comp Polynomial.C).toAlgebra
  rw [Valuation.mem_valuationSubring_iff]
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [ι.map_add]
    exact (v.map_add (ι p) (ι q)).trans (max_le hp hq)
  · intro n a
    have hC : v (ι (Polynomial.C a)) ≤ 1 := by
      change v (algebraMap k F a) ≤ 1
      exact FiniteField.valuation_algebraMap_le_one v a
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ι.map_mul, ι.map_pow,
      v.map_mul, v.map_pow]
    exact mul_le_one₀ hC zero_le' (pow_le_one₀ zero_le' hX)
theorem affineIntegralClosureComposite_eq_chartMap
    {k F : Type*} [Field k] [Field F] [Algebra k[X] F] :
    (algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F)) =
    algebraMap k[X] F := by
  exact IsScalarTower.algebraMap_eq k[X] (FunctionField.ringOfIntegers k F) F
theorem ringOfIntegers_le_valuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k[X] F]
    (v : Valuation F ℤᵐ⁰)
    (ht : v (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (FunctionField.ringOfIntegers k F).toSubring ≤ v.valuationSubring.toSubring := by
  let B := FunctionField.ringOfIntegers k F
  let ι : k[X] →+* F := (algebraMap B F).comp (algebraMap k[X] B)
  have hX : v (ι Polynomial.X) ≤ 1 := ht
  have hpoly : ∀ p : k[X], ι p ∈ v.valuationSubring :=
    fun p ↦ polynomial_map_mem_valuationSubring ι v hX p
  change (integralClosure k[X] F).toSubring ≤ v.integer
  letI : IsIntegrallyClosedIn v.integer F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mp inferInstance
  rw [Subring.integralClosure_le_iff]
  intro p
  rw [← affineIntegralClosureComposite_eq_chartMap (k := k) (F := F)]
  exact hpoly p
noncomputable def ringOfIntegersToValuationRing
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k[X] F]
    (v : Valuation F ℤᵐ⁰)
    (ht : v (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    FunctionField.ringOfIntegers k F →+* v.valuationSubring := by
  let hB := ringOfIntegers_le_valuationSubring (v := v) ht
  exact (algebraMap (FunctionField.ringOfIntegers k F) F).codRestrict
    v.valuationSubring fun b => by
      change (b : F) ∈ v.valuationSubring
      exact hB b.property
noncomputable def regularCentreIdeal
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    Ideal (FunctionField.ringOfIntegers k F) :=
  (IsLocalRing.maximalIdeal P.valuation.valuationSubring).comap
    (ringOfIntegersToValuationRing (v := P.valuation) ht)
theorem regularCentreIdeal_isPrime
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (regularCentreIdeal P ht).IsPrime := by
  dsimp [regularCentreIdeal]
  exact (IsLocalRing.maximalIdeal P.valuation.valuationSubring).comap_isPrime _
theorem exists_nonzero_mem_regularCentreIdeal
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ∃ a : FunctionField.ringOfIntegers k F,
      a ≠ 0 ∧ a ∈ regularCentreIdeal P ht := by
  let B := FunctionField.ringOfIntegers k F
  obtain ⟨a, s, hs, hfrac⟩ :=
    IsFractionRing.div_surjective B P.uniformizer
  have hs0 : algebraMap B F s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hu0 : P.uniformizer ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hu_lt_one : P.valuation P.uniformizer < 1 := by
    rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hB := ringOfIntegers_le_valuationSubring (v := P.valuation) ht
  have hs_mem : algebraMap B F s ∈ P.valuation.valuationSubring := by
    change (s : F) ∈ P.valuation.valuationSubring
    exact hB s.property
  have hs_le_one : P.valuation (algebraMap B F s) ≤ 1 :=
    (P.valuation.mem_valuationSubring_iff _).mp hs_mem
  have hprod : algebraMap B F a =
      P.uniformizer * algebraMap B F s := by
    calc
      algebraMap B F a =
          (algebraMap B F a / algebraMap B F s) * algebraMap B F s :=
        (div_mul_cancel₀ _ hs0).symm
      _ = P.uniformizer * algebraMap B F s := by rw [hfrac]
  have ha0 : a ≠ 0 := by
    intro ha
    have hzero : P.uniformizer * algebraMap B F s = 0 := by
      simpa [ha] using hprod.symm
    exact (mul_ne_zero hu0 hs0) hzero
  have ha_lt_one : P.valuation (algebraMap B F a) < 1 := by
    calc
      P.valuation (algebraMap B F a) =
          P.valuation P.uniformizer * P.valuation (algebraMap B F s) := by
        rw [hprod, P.valuation.map_mul]
      _ ≤ P.valuation P.uniformizer * 1 :=
        mul_le_mul_of_nonneg_left hs_le_one
          (le_of_lt (by rw [P.valuation_uniformizer]; exact WithZero.exp_pos))
      _ = P.valuation P.uniformizer := mul_one _
      _ < 1 := hu_lt_one
  have ha_maximal :
      ringOfIntegersToValuationRing (v := P.valuation) ht a ∈
        IsLocalRing.maximalIdeal P.valuation.valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact ha_lt_one
  refine ⟨a, ha0, ?_⟩
  change ringOfIntegersToValuationRing (v := P.valuation) ht a ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  exact ha_maximal
theorem regularCentreIdeal_ne_bot
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreIdeal P ht ≠ ⊥ := by
  obtain ⟨a, ha0, haCentre⟩ := exists_nonzero_mem_regularCentreIdeal P ht
  intro hbot
  exact ha0 (Ideal.mem_bot.mp (hbot ▸ haCentre))
noncomputable def regularCentreHeightOne
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k F) :=
  ⟨regularCentreIdeal P ht, regularCentreIdeal_isPrime P ht,
    regularCentreIdeal_ne_bot P ht⟩
theorem regularCentre_primeCompl_maps_to_unit
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1)
    (s : (regularCentreHeightOne P ht).asIdeal.primeCompl) :
    IsUnit (ringOfIntegersToValuationRing (v := P.valuation) ht s) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hs
  apply s.property
  change ringOfIntegersToValuationRing (v := P.valuation) ht (s :
    FunctionField.ringOfIntegers k F) ∈
      IsLocalRing.maximalIdeal P.valuation.valuationSubring
  exact hs
noncomputable abbrev regularCentreCanonicalLocalization
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ValuationSubring F :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
    (regularCentreHeightOne P ht)
noncomputable def regularCentreLocalizationToValuationRing
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreCanonicalLocalization P ht →+*
      P.valuation.valuationSubring :=
  IsLocalization.lift
    (M := (regularCentreHeightOne P ht).asIdeal.primeCompl)
    (g := ringOfIntegersToValuationRing (v := P.valuation) ht)
    (regularCentre_primeCompl_maps_to_unit P ht)
theorem regularCentreLocalizationToValuationRing_comp
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (regularCentreLocalizationToValuationRing P ht).comp
      (algebraMap (FunctionField.ringOfIntegers k F)
        (regularCentreCanonicalLocalization P ht)) =
      ringOfIntegersToValuationRing (v := P.valuation) ht := by
  simpa [regularCentreLocalizationToValuationRing] using
    (IsLocalization.lift_comp (regularCentre_primeCompl_maps_to_unit P ht))
theorem regularCentreLocalization_coe_triangle
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (ValuationSubring.subtype P.valuation.valuationSubring).comp
      (regularCentreLocalizationToValuationRing P ht) =
      ValuationSubring.subtype (regularCentreCanonicalLocalization P ht) := by
  apply IsLocalization.ringHom_ext
    (regularCentreHeightOne P ht).asIdeal.primeCompl
  ext b
  change ((regularCentreLocalizationToValuationRing P ht
      (algebraMap (FunctionField.ringOfIntegers k F)
        (regularCentreCanonicalLocalization P ht) b) :
        P.valuation.valuationSubring) : F) = algebraMap
      (FunctionField.ringOfIntegers k F) F b
  rw [← RingHom.comp_apply, regularCentreLocalizationToValuationRing_comp]
  rfl
theorem regularCentreCanonicalLocalization_le_placeValuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreCanonicalLocalization P ht ≤ P.valuation.valuationSubring := by
  intro x hx
  let xC : regularCentreCanonicalLocalization P ht := ⟨x, hx⟩
  have htriangle := RingHom.congr_fun
    (regularCentreLocalization_coe_triangle P ht) xC
  have hxF :
      ((regularCentreLocalizationToValuationRing P ht xC :
        P.valuation.valuationSubring) : F) = x := by
    simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using htriangle
  rw [← hxF]
  exact (regularCentreLocalizationToValuationRing P ht xC).property
theorem globalPlace_valuation_isNontrivial
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : GlobalPlace k F) : P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
theorem globalPlace_valuationSubring_ne_top
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : GlobalPlace k F) : P.valuation.valuationSubring ≠ ⊤ := by
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff (v := P.valuation)).mp htop)
    (globalPlace_valuation_isNontrivial P)
theorem regularCentreCanonicalLocalization_eq_placeValuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    regularCentreCanonicalLocalization P ht = P.valuation.valuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _
    (regularCentreCanonicalLocalization_le_placeValuationSubring P ht)
    (globalPlace_valuationSubring_ne_top P)
theorem placeValuation_isEquiv_regularCentreAdicValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    P.valuation.IsEquiv ((regularCentreHeightOne P ht).valuation F) := by
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact (regularCentreCanonicalLocalization_eq_placeValuationSubring P ht).symm.trans
    ((regularCentreHeightOne P ht).valuationSubringAtPrime_eq_valuationSubring)
theorem placeValuation_eq_regularCentreAdicValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    P.valuation = (regularCentreHeightOne P ht).valuation F := by
  exact valuation_eq_of_surjective_isEquiv_withZeroMulInt
    P.valuation
    ((regularCentreHeightOne P ht).valuation F)
    P.normalized
    ((regularCentreHeightOne P ht).valuation_surjective F)
    (placeValuation_isEquiv_regularCentreAdicValuation P ht)
abbrev regularCoordinatePlaces
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] : Type _ :=
  { P : GlobalPlace k F //
    P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1 }
noncomputable def regularCentreHeightOneOnRegularCoordinatePlaces
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    regularCoordinatePlaces k F →
      IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k F) :=
  fun P ↦ regularCentreHeightOne P.1 P.2
theorem globalPlace_eq_of_valuation_eq
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    {P Q : GlobalPlace k F} (hvaluation : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases hvaluation
  rfl
noncomputable def originalCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  ρ.algebraMap RatFunc.X
noncomputable def originalInverseCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  (originalCoordinate ρ)⁻¹
theorem originalCoordinate_ne_zero
    {k F : Type*} [Field k] [Finite k] [Field F]
    [ρ : Algebra k⟮X⟯ F] [_root_.FunctionField k F] :
    originalCoordinate ρ ≠ 0 := by
  exact (map_ne_zero_iff ρ.algebraMap ρ.algebraMap.injective).mpr RatFunc.X_ne_zero
theorem original_coordinate_dichotomy
    {k F : Type*} [Field k] [Finite k] [Field F]
    [ρ : Algebra k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    P.valuation (originalCoordinate ρ) ≤ 1 ∨
      P.valuation (originalInverseCoordinate ρ) < 1 := by
  by_cases h : P.valuation (originalCoordinate ρ) ≤ 1
  · exact Or.inl h
  · right
    rw [originalInverseCoordinate, P.valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ (lt_of_not_ge h)
noncomputable def repackageRawGlobalPlace
    {k F : Type*} [Field k] [Finite k] [Field F]
    (A : Algebra k F) {A₀ : Algebra k F}
    (P : @GlobalPlace k F _ _ _ A₀) : @GlobalPlace k F _ _ _ A := by
  exact @GlobalPlace.mk k F _ _ _ A
    (@GlobalPlace.valuation k F _ _ _ A₀ P)
    (@GlobalPlace.normalized k F _ _ _ A₀ P)
theorem repackageRawGlobalPlace_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    (A : Algebra k F) {A₀ : Algebra k F}
    (P : @GlobalPlace k F _ _ _ A₀) :
    @GlobalPlace.valuation k F _ _ _ A (repackageRawGlobalPlace A P) =
      @GlobalPlace.valuation k F _ _ _ A₀ P := rfl
theorem directIntegralCoordinate_eq_originalCoordinate
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    algebraMap (_root_.FunctionField.ringOfIntegers k F) F
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) =
        originalCoordinate ρ := by
  change ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))) Polynomial.X =
      ρ.algebraMap RatFunc.X
  calc
    _ = (algebraMap k[X] F) Polynomial.X := by
      rw [← IsScalarTower.algebraMap_eq k[X]
        (_root_.FunctionField.ringOfIntegers k F) F]
    _ = ρ.algebraMap ((algebraMap k[X] k⟮X⟯) Polynomial.X) := by
      rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F]
    _ = ρ.algebraMap RatFunc.X := rfl
theorem inverseIntegralCoordinate_eq_originalInverseCoordinate
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    algebraMap (_root_.FunctionField.ringOfIntegers k F) F
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) =
        originalInverseCoordinate ρ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  change ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))) Polynomial.X =
      originalInverseCoordinate ρ
  calc
    _ = (algebraMap k[X] F) Polynomial.X := by
      rw [← IsScalarTower.algebraMap_eq k[X]
        (_root_.FunctionField.ringOfIntegers k F) F]
    _ = InverseAffinePlace.transportedPolynomialMap (oldRationalAlgebra := ρ) k F Polynomial.X := rfl
    _ = InverseAffinePlace.transportedRationalMap (oldRationalAlgebra := ρ) k F RatFunc.X := by
      rfl
    _ = originalInverseCoordinate ρ := by
      change ρ.algebraMap (InverseAffinePlace.rationalInvolution k RatFunc.X) =
        (ρ.algebraMap RatFunc.X)⁻¹
      rw [InverseAffinePlace.rationalInvolution_X, map_inv₀]
theorem regularCentreHeightOne_mem_of_lt_one
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (hbound : P.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1)
    (a : _root_.FunctionField.ringOfIntegers k F)
    (ha : P.valuation (algebraMap (_root_.FunctionField.ringOfIntegers k F) F a) < 1) :
    a ∈ (regularCentreHeightOne P hbound).asIdeal := by
  change ringOfIntegersToValuationRing (v := P.valuation) hbound a ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  change P.valuation (algebraMap (_root_.FunctionField.ringOfIntegers k F) F a) < 1
  exact ha
noncomputable def inverseCentreInInfinityFibre
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation (originalInverseCoordinate ρ) < 1) :
    InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  let Pinv : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) :=
    repackageRawGlobalPlace (AffinePlace.constantAlgebra k F) P
  let hbound : Pinv.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
    le_of_lt (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv)
  let C := regularCentreHeightOne Pinv hbound
  refine ⟨C, ?_⟩
  apply Ideal.dvd_iff_le.mpr
  change Ideal.map (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (Polynomial.idealX k).asIdeal ≤ C.asIdeal
  rw [Ideal.map_le_iff_le_comap, Polynomial.idealX_span, Ideal.span_le,
    Set.singleton_subset_iff]
  exact Ideal.mem_comap.mpr (regularCentreHeightOne_mem_of_lt_one Pinv hbound
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv))
noncomputable def inverseFibreRawValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) : Valuation F ℤᵐ⁰ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  exact @GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)
    (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D)
theorem inverseFibreRawValuation_eq_ambient
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    inverseFibreRawValuation (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D =
      D.1.valuation F := by
  unfold inverseFibreRawValuation
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  rw [@InverseAffinePlace.globalPlace_valuation k F _ _ _ π ρ τ φ σ D]
  rfl
noncomputable def inverseFibreGlobalPlaceAt
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (κ : Algebra k F)
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace k F _ _ _ κ :=
  repackageRawGlobalPlace κ
    (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D)
theorem inverseCentre_rawValuation_eq_ambient
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation (originalInverseCoordinate ρ) < 1) :
    P.valuation = inverseFibreRawValuation
      (inverseCentreInInfinityFibre P hinv) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  let Pinv : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) :=
    repackageRawGlobalPlace (AffinePlace.constantAlgebra k F) P
  let hbound : Pinv.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
    le_of_lt (by
      rw [inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv)
  let D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F :=
    inverseCentreInInfinityFibre (π := π) (ρ := ρ) (τ := τ) (φ := φ)
      (σ := σ) (κ := κ) P hinv
  calc
    @GlobalPlace.valuation k F _ _ _ κ P =
        @GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F) Pinv :=
      (repackageRawGlobalPlace_valuation (AffinePlace.constantAlgebra k F) P).symm
    _ = (regularCentreHeightOne Pinv hbound).valuation F :=
      placeValuation_eq_regularCentreAdicValuation Pinv hbound
    _ = inverseFibreRawValuation (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D := by
      rw [inverseFibreRawValuation_eq_ambient
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      rfl
theorem inverseFibreRawValuation_surjective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    Function.Surjective (inverseFibreRawValuation D) := by
  unfold inverseFibreRawValuation
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  exact @GlobalPlace.normalized k F _ _ _ (AffinePlace.constantAlgebra k F)
    (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D)
theorem inverseFibreRawValuation_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D E : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F)
    (h : inverseFibreRawValuation D = inverseFibreRawValuation E) : D = E := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  apply Subtype.ext
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
  apply Valuation.IsEquiv.of_eq
  rw [inverseFibreRawValuation_eq_ambient
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D,
    inverseFibreRawValuation_eq_ambient
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) E] at h
  exact h
theorem inverseFibreRawValuation_originalInverse_lt_one
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    inverseFibreRawValuation D (originalInverseCoordinate ρ) < 1 := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  rw [inverseFibreRawValuation_eq_ambient
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
  rw [← inverseIntegralCoordinate_eq_originalInverseCoordinate
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
  exact InverseAffinePlace.globalPlace_coordinate_valuation_lt_one
    (oldPolynomialAlgebra := π) (oldRationalAlgebra := ρ) (oldScalarTower := τ)
    (oldFunctionField := φ) (oldSeparable := σ) k F D
noncomputable abbrev CorrectedTwoChartPlace
    (k F : Type*) [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] : Type _ :=
  Sum (AffinePlace.carrier k F) (InverseAffinePlace.infinityFibre k F)
noncomputable def correctedTwoChartValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    CorrectedTwoChartPlace k F → Valuation F ℤᵐ⁰
  | .inl C => C.valuation F
  | .inr D => inverseFibreRawValuation D
noncomputable def correctedTwoChartToGlobalPlace
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    CorrectedTwoChartPlace k F → @GlobalPlace k F _ _ _ κ
  | .inl C => ⟨C.valuation F, C.valuation_surjective F⟩
  | .inr D => ⟨inverseFibreRawValuation D, inverseFibreRawValuation_surjective D⟩
theorem correctedTwoChartToGlobalPlace_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : CorrectedTwoChartPlace k F) :
    (correctedTwoChartToGlobalPlace C).valuation = correctedTwoChartValuation C := by
  cases C <;> rfl
theorem everyGlobalPlace_has_correctedTwoChartWitness
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    ∃ C : CorrectedTwoChartPlace k F,
      P.valuation = correctedTwoChartValuation C := by
  rcases original_coordinate_dichotomy P with hdirect | hinverse
  · let hbound : P.valuation
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 := by
      rw [directIntegralCoordinate_eq_originalCoordinate]
      exact hdirect
    exact ⟨Sum.inl (regularCentreHeightOne P hbound),
      placeValuation_eq_regularCentreAdicValuation P hbound⟩
  · let D := inverseCentreInInfinityFibre P hinverse
    exact ⟨Sum.inr D, inverseCentre_rawValuation_eq_ambient P hinverse⟩
theorem directImage_ne_inverseFibreImage
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : AffinePlace.carrier k F) (D : InverseAffinePlace.infinityFibre k F) :
    correctedTwoChartToGlobalPlace (Sum.inl C : CorrectedTwoChartPlace k F) ≠
      correctedTwoChartToGlobalPlace (Sum.inr D : CorrectedTwoChartPlace k F) := by
  intro h
  have hval : C.valuation F = inverseFibreRawValuation D := by
    change (correctedTwoChartToGlobalPlace
      (Sum.inl C : CorrectedTwoChartPlace k F)).valuation =
      (correctedTwoChartToGlobalPlace (Sum.inr D : CorrectedTwoChartPlace k F)).valuation
    exact congrArg (@GlobalPlace.valuation k F _ _ _ κ) h
  have hdirect : C.valuation F (originalCoordinate ρ) ≤ 1 := by
    rw [← directIntegralCoordinate_eq_originalCoordinate]
    exact C.valuation_le_one _
  have hinverse : 1 < inverseFibreRawValuation D (originalCoordinate ρ) := by
    have hy := inverseFibreRawValuation_originalInverse_lt_one (ρ := ρ) D
    rw [originalInverseCoordinate, (inverseFibreRawValuation D).map_inv] at hy
    exact (inv_lt_one₀ ((inverseFibreRawValuation D).pos_iff.mpr
      (originalCoordinate_ne_zero (ρ := ρ)))).mp hy
  apply (not_lt_of_ge hdirect)
  rw [hval.symm] at hinverse
  exact hinverse
theorem correctedTwoChartToGlobalPlace_bijective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    Function.Bijective (correctedTwoChartToGlobalPlace (k := k) (F := F)) := by
  constructor
  · intro C D h
    cases C <;> cases D
    · exact congrArg Sum.inl (by
        apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
        exact Valuation.IsEquiv.of_eq (congrArg (@GlobalPlace.valuation k F _ _ _ κ) h))
    · exact False.elim (directImage_ne_inverseFibreImage _ _ h)
    · exact False.elim (directImage_ne_inverseFibreImage _ _ h.symm)
    · exact congrArg Sum.inr
        (inverseFibreRawValuation_injective (ρ := ρ) _ _
          (congrArg (@GlobalPlace.valuation k F _ _ _ κ) h))
  · intro P
    obtain ⟨C, hC⟩ := everyGlobalPlace_has_correctedTwoChartWitness P
    refine ⟨C, ?_⟩
    apply globalPlace_eq_of_valuation_eq
    rw [correctedTwoChartToGlobalPlace_valuation]
    exact hC.symm
noncomputable def correctedTwoChartGlobalPlaceEquiv
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    CorrectedTwoChartPlace k F ≃ @GlobalPlace k F _ _ _ κ :=
  Equiv.ofBijective (correctedTwoChartToGlobalPlace (k := k) (F := F))
    (correctedTwoChartToGlobalPlace_bijective (k := k) (F := F))
noncomputable def inverseFibrePrincipalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) : Divisor (InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Fintype (InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :=
    InverseAffinePlace.infinityFibreFintype (oldRationalAlgebra := ρ) k F
  exact Finsupp.onFinset Finset.univ
    (fun D => -WithZero.log (inverseFibreRawValuation
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D (f : F)))
    (by intro D _; exact Finset.mem_univ D)
noncomputable def twoChartPrincipalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) : Divisor (CorrectedTwoChartPlace k F) :=
  Finsupp.mapDomain Sum.inl (AffinePlace.affinePrincipalDivisor k F f) +
    Finsupp.mapDomain Sum.inr (inverseFibrePrincipalDivisor (k := k) (F := F) f)
noncomputable def chartGlobalPlaceEquiv
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F] :
    CorrectedTwoChartPlace k F ≃ @GlobalPlace k F _ _ _ κ :=
  correctedTwoChartGlobalPlaceEquiv (k := k) (F := F)
theorem chartGlobalPlaceEquiv_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : CorrectedTwoChartPlace k F) :
    chartGlobalPlaceEquiv (k := k) (F := F) C = correctedTwoChartToGlobalPlace C := rfl
noncomputable def GlobalPlace.principalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) : Divisor (@GlobalPlace k F _ _ _ κ) :=
  Finsupp.equivMapDomain (chartGlobalPlaceEquiv (k := k) (F := F))
    (twoChartPrincipalDivisor (k := k) (F := F) f)
noncomputable def inverseFibreResidueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) : ℕ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  exact AffinePlace.residueDegree k F D.1
noncomputable def twoChartResidueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] :
    CorrectedTwoChartPlace k F → ℕ
  | .inl C => AffinePlace.residueDegree k F C
  | .inr D => inverseFibreResidueDegree (k := k) (F := F) D
noncomputable def GlobalPlace.repackage
    {k F : Type*} [Field k] [Finite k] [Field F]
    {oldAlgebra : Algebra k F} (newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace k F _ _ _ newAlgebra :=
  repackageRawGlobalPlace newAlgebra P
noncomputable def GlobalPlace.repackageEquiv
    {k F : Type*} [Field k] [Finite k] [Field F]
    (oldAlgebra newAlgebra : Algebra k F) :
    @GlobalPlace k F _ _ _ oldAlgebra ≃
      @GlobalPlace k F _ _ _ newAlgebra where
  toFun := GlobalPlace.repackage newAlgebra
  invFun := GlobalPlace.repackage oldAlgebra
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl
noncomputable def InverseAffinePlace.infinityFibreGlobalPlace
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace k F _ _ _ κ :=
  inverseFibreGlobalPlaceAt
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D
theorem affineGlobalPlace_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra (RatFunc k) F]
    [IsScalarTower k[X] (RatFunc k) F]
    [_root_.FunctionField k F] [Algebra.IsSeparable (RatFunc k) F] :
    Function.Injective (AffinePlace.globalPlace k F) := by
  intro C D hCD
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
    (K := F)
  exact Valuation.IsEquiv.of_eq
    (congrArg
      (@GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)) hCD)
theorem infinityFibreGlobalPlace_injective
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F] :
    Function.Injective
      (InverseAffinePlace.infinityFibreGlobalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
        (κ := AffinePlace.constantAlgebra k F)) := by
  intro C D hCD
  apply inverseFibreRawValuation_injective (ρ := ρ)
  exact congrArg
    (@GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)) hCD
noncomputable def GlobalPlace.affineFinsupp
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [Algebra k[X] F] [Algebra (RatFunc k) F]
    [IsScalarTower k[X] (RatFunc k) F]
    [_root_.FunctionField k F] [Algebra.IsSeparable (RatFunc k) F]
    [Zero M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    AffinePlace.carrier k F →₀ M :=
  Finsupp.comapDomain (AffinePlace.globalPlace k F) f
    (affineGlobalPlace_injective (k := k) (F := F)).injOn
noncomputable def GlobalPlace.infinityFibreFinsupp
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F]
    [Zero M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F →₀ M :=
  Finsupp.comapDomain
    (InverseAffinePlace.infinityFibreGlobalPlace
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
      (κ := AffinePlace.constantAlgebra k F)) f
    (infinityFibreGlobalPlace_injective
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)).injOn
noncomputable def InverseAffinePlace.infinityFibrePrincipalDivisor
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) : Divisor (InverseAffinePlace.infinityFibre k F) :=
  inverseFibrePrincipalDivisor (k := k) (F := F) f
noncomputable def InverseAffinePlace.infinityFibreResidueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (D : InverseAffinePlace.infinityFibre k F) : ℕ :=
  inverseFibreResidueDegree (k := k) (F := F) D
noncomputable def GlobalPlace.residueDegree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) : ℕ :=
  twoChartResidueDegree (k := k) (F := F)
    ((chartGlobalPlaceEquiv (k := k) (F := F)).symm P)
theorem GlobalPlace.finite_residueField
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) : Finite (GlobalPlace.residueField P) := by
  let C := (chartGlobalPlaceEquiv (k := k) (F := F)).symm P
  have hP : chartGlobalPlaceEquiv (k := k) (F := F) C = P :=
    (chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply P
  rw [← hP, chartGlobalPlaceEquiv_apply]
  rcases C with C | D
  · letI : Finite (AffinePlace.residueField k F C) :=
      AffinePlace.finite_residueField k F C
    let e₁ : Localization.AtPrime C.asIdeal ≃+*
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C :=
      (Localization.algEquiv C.asIdeal.primeCompl
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C)).toRingEquiv
    let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C ≃+*
        (C.valuation F).valuationSubring := by
      rw [C.valuationSubringAtPrime_eq_valuationSubring]
    exact Finite.of_equiv (AffinePlace.residueField k F C)
      (IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)).toEquiv
  · letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    letI : Finite (AffinePlace.residueField k F D.1) :=
      AffinePlace.finite_residueField k F D.1
    let e₁ : Localization.AtPrime D.1.asIdeal ≃+*
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F D.1 :=
      (Localization.algEquiv D.1.asIdeal.primeCompl
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F D.1)).toRingEquiv
    let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F D.1 ≃+*
        (inverseFibreRawValuation (π := π) (ρ := ρ) (τ := τ) (φ := φ)
          (σ := σ) D).valuationSubring := by
      rw [D.1.valuationSubringAtPrime_eq_valuationSubring,
        inverseFibreRawValuation_eq_ambient (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (σ := σ)]
    exact Finite.of_equiv (AffinePlace.residueField k F D.1)
      (IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)).toEquiv
theorem GlobalPlace.residueField_finiteDimensional
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
    FiniteDimensional k (GlobalPlace.residueField P) := by
  letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
  letI : Finite (GlobalPlace.residueField P) := GlobalPlace.finite_residueField P
  exact (Module.finite_iff_finite).mpr inferInstance
end QEC.Coding.AlgebraicGeometry


