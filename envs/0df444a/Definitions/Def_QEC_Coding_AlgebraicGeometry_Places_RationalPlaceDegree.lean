-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
-- name    : QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:19:27.222182+00:00
-- url     : https://prove2.me/theorems/01afabe8-c1b9-403c-be68-ced4b29c2584
-- title:
--   Rational Place Degree
-- statement:
--   Definitions and structural lemmas for Rational Place Degree, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlaceDegree.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
noncomputable def rationalPlaceDegree_normalizedValueGroupOrderIso
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] : ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰ :=
  Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v
noncomputable def rationalPlaceDegree_normalizedCodomainOrderAuto
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) : ℤᵐ⁰ ≃*o ℤᵐ⁰ :=
  (rationalPlaceDegree_normalizedValueGroupOrderIso v).symm.trans
    ((h.orderMonoidIso).trans (rationalPlaceDegree_normalizedValueGroupOrderIso w))
noncomputable def rationalPlaceDegree_normalizedUnitOrderAuto
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : Multiplicative ℤ ≃*o Multiplicative ℤ :=
  OrderMonoidIso.withZero.symm φ
theorem rationalPlaceDegree_polynomial_map_mem_valuationSubring
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
theorem rationalPlaceDegree_affineIntegralClosureComposite_eq_chartMap
    {k F : Type*} [Field k] [Field F] [Algebra k[X] F] :
    (algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F)) =
    algebraMap k[X] F := by
  exact IsScalarTower.algebraMap_eq k[X] (FunctionField.ringOfIntegers k F) F
theorem rationalPlaceDegree_ringOfIntegers_le_valuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k[X] F]
    (v : Valuation F ℤᵐ⁰)
    (ht : v (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (FunctionField.ringOfIntegers k F).toSubring ≤ v.valuationSubring.toSubring := by
  let B := FunctionField.ringOfIntegers k F
  let ι : k[X] →+* F := (algebraMap B F).comp (algebraMap k[X] B)
  have hX : v (ι Polynomial.X) ≤ 1 := ht
  have hpoly : ∀ p : k[X], ι p ∈ v.valuationSubring :=
    fun p ↦ rationalPlaceDegree_polynomial_map_mem_valuationSubring ι v hX p
  change (integralClosure k[X] F).toSubring ≤ v.integer
  letI : IsIntegrallyClosedIn v.integer F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mp inferInstance
  rw [Subring.integralClosure_le_iff]
  intro p
  rw [← rationalPlaceDegree_affineIntegralClosureComposite_eq_chartMap (k := k) (F := F)]
  exact hpoly p
noncomputable def rationalPlaceDegree_ringOfIntegersToValuationRing
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k[X] F]
    (v : Valuation F ℤᵐ⁰)
    (ht : v (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    FunctionField.ringOfIntegers k F →+* v.valuationSubring := by
  let hB := rationalPlaceDegree_ringOfIntegers_le_valuationSubring (v := v) ht
  exact (algebraMap (FunctionField.ringOfIntegers k F) F).codRestrict
    v.valuationSubring fun b => by
      change (b : F) ∈ v.valuationSubring
      exact hB b.property
noncomputable def rationalPlaceDegree_regularCentreIdeal
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    Ideal (FunctionField.ringOfIntegers k F) :=
  (IsLocalRing.maximalIdeal P.valuation.valuationSubring).comap
    (rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht)
theorem rationalPlaceDegree_regularCentreIdeal_isPrime
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (rationalPlaceDegree_regularCentreIdeal P ht).IsPrime := by
  dsimp [rationalPlaceDegree_regularCentreIdeal]
  exact (IsLocalRing.maximalIdeal P.valuation.valuationSubring).comap_isPrime _
theorem rationalPlaceDegree_exists_nonzero_mem_regularCentreIdeal
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ∃ a : FunctionField.ringOfIntegers k F,
      a ≠ 0 ∧ a ∈ rationalPlaceDegree_regularCentreIdeal P ht := by
  let B := FunctionField.ringOfIntegers k F
  obtain ⟨a, s, hs, hfrac⟩ := IsFractionRing.div_surjective B P.uniformizer
  have hs0 : algebraMap B F s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hu0 : P.uniformizer ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hu_lt_one : P.valuation P.uniformizer < 1 := by
    rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hB := rationalPlaceDegree_ringOfIntegers_le_valuationSubring (v := P.valuation) ht
  have hs_mem : algebraMap B F s ∈ P.valuation.valuationSubring := by
    change (s : F) ∈ P.valuation.valuationSubring
    exact hB s.property
  have hs_le_one : P.valuation (algebraMap B F s) ≤ 1 :=
    (P.valuation.mem_valuationSubring_iff _).mp hs_mem
  have hprod : algebraMap B F a = P.uniformizer * algebraMap B F s := by
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
      rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht a ∈
        IsLocalRing.maximalIdeal P.valuation.valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    exact ha_lt_one
  refine ⟨a, ha0, ?_⟩
  change rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht a ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  exact ha_maximal
theorem rationalPlaceDegree_regularCentreIdeal_ne_bot
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    rationalPlaceDegree_regularCentreIdeal P ht ≠ ⊥ := by
  obtain ⟨a, ha0, haCentre⟩ := rationalPlaceDegree_exists_nonzero_mem_regularCentreIdeal P ht
  intro hbot
  exact ha0 (Ideal.mem_bot.mp (hbot ▸ haCentre))
noncomputable def rationalPlaceDegree_regularCentreHeightOne
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k F) :=
  ⟨rationalPlaceDegree_regularCentreIdeal P ht, rationalPlaceDegree_regularCentreIdeal_isPrime P ht,
    rationalPlaceDegree_regularCentreIdeal_ne_bot P ht⟩
theorem rationalPlaceDegree_regularCentre_primeCompl_maps_to_unit
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1)
    (s : (rationalPlaceDegree_regularCentreHeightOne P ht).asIdeal.primeCompl) :
    IsUnit (rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht s) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hs
  apply s.property
  change rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht (s :
    FunctionField.ringOfIntegers k F) ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  exact hs
noncomputable abbrev rationalPlaceDegree_regularCentreCanonicalLocalization
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    ValuationSubring F :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F
    (rationalPlaceDegree_regularCentreHeightOne P ht)
noncomputable def rationalPlaceDegree_regularCentreLocalizationToValuationRing
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    rationalPlaceDegree_regularCentreCanonicalLocalization P ht →+*
      P.valuation.valuationSubring :=
  IsLocalization.lift
    (M := (rationalPlaceDegree_regularCentreHeightOne P ht).asIdeal.primeCompl)
    (g := rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht)
    (rationalPlaceDegree_regularCentre_primeCompl_maps_to_unit P ht)
theorem rationalPlaceDegree_regularCentreHeightOne_mem_of_lt_one
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
    a ∈ (rationalPlaceDegree_regularCentreHeightOne P hbound).asIdeal := by
  change rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) hbound a ∈
    IsLocalRing.maximalIdeal P.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  change P.valuation (algebraMap (_root_.FunctionField.ringOfIntegers k F) F a) < 1
  exact ha
noncomputable def rationalPlaceDegree_affineResidueFieldEquiv
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F) (C : AffinePlace.carrier k F)
    (hvaluation : P.valuation = C.valuation F) :
    AffinePlace.residueField k F C ≃+* GlobalPlace.residueField P := by
  change IsLocalRing.ResidueField (Localization.AtPrime C.asIdeal) ≃+*
    IsLocalRing.ResidueField P.valuation.valuationSubring
  let e₁ : Localization.AtPrime C.asIdeal ≃+*
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C :=
    (Localization.algEquiv C.asIdeal.primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C)).toRingEquiv
  let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C ≃+*
      P.valuation.valuationSubring := by
    rw [C.valuationSubringAtPrime_eq_valuationSubring, hvaluation]
  exact IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)
noncomputable def rationalPlaceDegree_originalCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  ρ.algebraMap RatFunc.X
noncomputable def rationalPlaceDegree_originalInverseCoordinate
    {k F : Type*} [Field k] [Field F] (ρ : Algebra k⟮X⟯ F) : F :=
  (rationalPlaceDegree_originalCoordinate ρ)⁻¹
theorem rationalPlaceDegree_inverseIntegralCoordinate_eq_originalInverseCoordinate
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
        rationalPlaceDegree_originalInverseCoordinate ρ := by
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
      rationalPlaceDegree_originalInverseCoordinate ρ
  calc
    _ = (algebraMap k[X] F) Polynomial.X := by
      rw [← IsScalarTower.algebraMap_eq k[X]
        (_root_.FunctionField.ringOfIntegers k F) F]
    _ = InverseAffinePlace.transportedPolynomialMap (oldRationalAlgebra := ρ) k F Polynomial.X := rfl
    _ = InverseAffinePlace.transportedRationalMap (oldRationalAlgebra := ρ) k F RatFunc.X := by
      rfl
    _ = rationalPlaceDegree_originalInverseCoordinate ρ := by
      change ρ.algebraMap (InverseAffinePlace.rationalInvolution k RatFunc.X) =
        (ρ.algebraMap RatFunc.X)⁻¹
      rw [InverseAffinePlace.rationalInvolution_X, map_inv₀]
noncomputable def rationalPlaceDegree_inverseCentreInInfinityFibre
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation (rationalPlaceDegree_originalInverseCoordinate ρ) < 1) :
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
  let hbound : P.valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
    le_of_lt (by
      rw [rationalPlaceDegree_inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv)
  let C := rationalPlaceDegree_regularCentreHeightOne P hbound
  refine ⟨C, ?_⟩
  apply Ideal.dvd_iff_le.mpr
  change Ideal.map (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (Polynomial.idealX k).asIdeal ≤ C.asIdeal
  rw [Ideal.map_le_iff_le_comap, Polynomial.idealX_span, Ideal.span_le,
    Set.singleton_subset_iff]
  exact Ideal.mem_comap.mpr (rationalPlaceDegree_regularCentreHeightOne_mem_of_lt_one P hbound
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) (by
      rw [rationalPlaceDegree_inverseIntegralCoordinate_eq_originalInverseCoordinate
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
      exact hinv))
end QEC.Coding.AlgebraicGeometry


