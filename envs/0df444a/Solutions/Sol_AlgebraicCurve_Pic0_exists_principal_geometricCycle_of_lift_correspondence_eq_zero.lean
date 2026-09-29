-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/41f5a3b3-8f7c-5825-8e80-4332810baec4

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "FundamentalIdentityAlong FiniteAlong NormFormulaAlong Divisor.correspondence Pic0.degZeroCorrespondence Pic0.correspondence Place Place.ord_inv Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal Divisor.mem_principal HasPrincipalDivisors Pic Pic0 IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension exists_baseChange_correspondence_of_constantFieldExtension Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero linearIndependent_of_constantFieldExtension Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed"
namespace GeometricCycleAssembly
p2m_open "AlgebraicCurve"

theorem lift_equivariant {ι A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (T : ι → A →+ A) (S : ι → B →+ B) (h : ∀ i a, f (T i a) = S i (f a))
    (q : FreeAlgebra ℤ ι) (a : A) :
    f (FreeAlgebra.lift ℤ (fun i => (T i).toIntLinearMap) q a) =
      FreeAlgebra.lift ℤ (fun i => (S i).toIntLinearMap) q (f a) := by
  induction q using FreeAlgebra.induction generalizing a with
  | grade0 r => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_zsmul]
  | grade1 i => simp only [FreeAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap, h]
  | mul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

section Centre

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE]

def Centred (P : Place E FE) (e : F →ₐ[K] E) : Prop :=
  ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1

theorem eq_zero_of_valuation_algebraMap_lt_one (P : Place E FE) {a : E}
    (ha : P.toValuationSubring.valuation (algebraMap E FE a) < 1) : a = 0 := by
  by_contra h
  have hne : algebraMap E FE a ≠ 0 := (map_ne_zero _).2 h
  have hinv : (algebraMap E FE a)⁻¹ ∈ P.toValuationSubring := by
    rw [← map_inv₀]; exact P.algebraMap_mem' a⁻¹
  have h1 : P.toValuationSubring.valuation ((algebraMap E FE a)⁻¹) ≤ 1 :=
    (P.toValuationSubring.valuation_le_one_iff _).mpr hinv
  have hlt : P.toValuationSubring.valuation (algebraMap E FE a * (algebraMap E FE a)⁻¹) < 1 := by
    rw [map_mul]
    calc P.toValuationSubring.valuation (algebraMap E FE a) *
          P.toValuationSubring.valuation ((algebraMap E FE a)⁻¹)
        ≤ P.toValuationSubring.valuation (algebraMap E FE a) * 1 := by gcongr
      _ = P.toValuationSubring.valuation (algebraMap E FE a) := mul_one _
      _ < 1 := ha
  rw [mul_inv_cancel₀ hne, map_one] at hlt
  exact lt_irrefl _ hlt

theorem Centred.eq {P : Place E FE} {e e' : F →ₐ[K] E} (he : Centred P e) (he' : Centred P e') :
    e = e' := by
  ext f
  have h := Valuation.map_sub_lt P.toValuationSubring.valuation (he' f) (he f)
  rw [sub_sub_sub_cancel_left, ← map_sub] at h
  exact sub_eq_zero.mp (eq_zero_of_valuation_algebraMap_lt_one P h)

theorem Centred.mem {P : Place E FE} {e : F →ₐ[K] E} (he : Centred P e) (f : F) :
    algebraMap F FE f ∈ P.toValuationSubring := by
  have h1 : algebraMap F FE f - algebraMap E FE (e f) ∈ P.toValuationSubring :=
    (P.toValuationSubring.valuation_le_one_iff _).mp (he f).le
  simpa using add_mem h1 (P.algebraMap_mem' (e f))

end Centre

theorem not_mem_of_ord_neg {k L : Type*} [Field k] [Field L] [Algebra k L] (v : Place k L)
    {f : L} (hf : f ≠ 0) (h : v.ord f < 0) : f ∉ v.toValuationSubring := by
  intro hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf) (by rw [Place.ord_inv]; omega)
  let u : v.toValuationSubringˣ :=
    ⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf), Subtype.ext (inv_mul_cancel₀ hf)⟩
  have hu := v.ord_coe_unit u
  change v.ord f = 0 at hu
  omega

end AlgebraicCurve.GeometricCycleAssembly

open AlgebraicCurve.GeometricCycleAssembly in
theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (η : F →ₐ[K] E) :
    ∃ (g : FE) (_ : g ≠ 0) (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E)),
      (∀ P ∈ S, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1) ∧
      (∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
        ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) ∧
      (∑ P ∈ S, Finsupp.single (y P) (P.ord g) : (F →ₐ[K] E) →₀ ℤ) =
        FreeAlgebra.lift ℤ (fun i => (Finsupp.liftAddHom fun e : F →ₐ[K] E =>
          zmultiplesHom ((F →ₐ[K] E) →₀ ℤ)
            (∑ᶠ σ ∈ {σ : F' i →ₐ[K] E | σ.comp (φ i) = e},
              Finsupp.single (σ.comp (ψ i)) (1 : ℤ))).toIntLinearMap) p (Finsupp.single η 1) := by
  classical

  obtain ⟨hC1, hC1b⟩ :=
    Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE hfgE hgen

  choose F'E instF instAE instAF' instAK instTE instTF' instC φE ψE hφE hψE hFIE hfinE hNE
    hfgE' hgen' hφcomm hψcomm hfib hcen hrat using
    fun i => exists_baseChange_correspondence_of_constantFieldExtension K F hfg (F' i) (φ i) (ψ i)
      (hφ i) (hψ i) (hFI i) (hfin i) (hN i) E FE hfgE hgen

  have hpE := Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero K F hfg F' φ ψ hφ hψ hFI
    hfin hN p hp E FE hfgE hgen F'E hfgE' hgen' φE ψE hφcomm hψcomm hφE hψE hFIE hfinE hNE

  set TZ : ι → (Divisor.degZero (K := E) (F := FE) →+ Divisor.degZero (K := E) (F := FE)) :=
    fun i => Pic0.degZeroCorrespondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) with hTZ
  set TD : ι → (Divisor E FE →+ Divisor E FE) :=
    fun i => Divisor.correspondence (φE i) (ψE i) (hφE i) (hψE i) with hTD
  set Z : ι → (F →ₐ[K] E) → ((F →ₐ[K] E) →₀ ℤ) := fun i e =>
    ∑ᶠ σ ∈ {σ : F' i →ₐ[K] E | σ.comp (φ i) = e}, Finsupp.single (σ.comp (ψ i)) (1 : ℤ) with hZ
  set TA : ι → (((F →ₐ[K] E) →₀ ℤ) →+ ((F →ₐ[K] E) →₀ ℤ)) := fun i =>
    Finsupp.liftAddHom fun e : F →ₐ[K] E => zmultiplesHom ((F →ₐ[K] E) →₀ ℤ) (Z i e) with hTA

  let ctrH : Place E FE → ℤ →+ ((F →ₐ[K] E) →₀ ℤ) := fun Q =>
    if h : ∃ e : F →ₐ[K] E, Centred Q e then Finsupp.singleAddHom h.choose else 0
  have ctrH_pos : ∀ {Q : Place E FE} (h : ∃ e : F →ₐ[K] E, Centred Q e),
      ctrH Q = Finsupp.singleAddHom h.choose := fun h => dif_pos h
  have ctrH_neg : ∀ {Q : Place E FE}, (¬ ∃ e : F →ₐ[K] E, Centred Q e) → ctrH Q = 0 :=
    fun h => dif_neg h
  set Φ : Divisor E FE →+ ((F →ₐ[K] E) →₀ ℤ) := Finsupp.liftAddHom ctrH with hΦdef

  have dichotomy : ∀ Q : Place E FE, (¬ ∃ e : F →ₐ[K] E, Centred Q e) →
      ∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring := by
    intro Q hQ
    by_contra hall
    push Not at hall
    exact hQ (hC1b Q hall)
  have not_centred_of_rat : ∀ Q : Place E FE, (∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring) →
      ¬ ∃ e : F →ₐ[K] E, Centred Q e := by
    rintro Q ⟨f, hf⟩ ⟨e, he⟩
    exact hf (he.mem f)

  have key : ∀ (i : ι) (P : Place E FE),
      Φ (TD i (Finsupp.single P 1)) = TA i (Φ (Finsupp.single P 1)) := by
    intro i P
    rw [hΦdef, Finsupp.liftAddHom_apply_single]
    by_cases hP : ∃ e : F →ₐ[K] E, Centred P e
    · have hc : Centred P hP.choose := hP.choose_spec
      rw [ctrH_pos hP, Finsupp.singleAddHom_apply, hTA, Finsupp.liftAddHom_apply_single,
        zmultiplesHom_apply, one_zsmul]
      ext e'
      obtain ⟨Q', hQ'c, hQ'u⟩ := hC1 e'
      rw [Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.finsetSum_apply,
        Finset.sum_eq_single Q']
      · have hQ' : ∃ e : F →ₐ[K] E, Centred Q' e := ⟨e', hQ'c⟩
        have hce : hQ'.choose = e' := Centred.eq hQ'.choose_spec hQ'c
        rw [ctrH_pos hQ', hce, Finsupp.singleAddHom_apply, Finsupp.single_eq_same]
        exact hfib i P hP.choose hc Q' e' hQ'c
      · intro Q hQ hne
        by_cases hQc : ∃ e : F →ₐ[K] E, Centred Q e
        · rw [ctrH_pos hQc, Finsupp.singleAddHom_apply, Finsupp.single_apply, if_neg]
          intro heq
          exact hne (hQ'u Q (heq ▸ hQc.choose_spec))
        · rw [ctrH_neg hQc, AddMonoidHom.zero_apply, Finsupp.zero_apply]
      · intro hnot
        rw [Finsupp.notMem_support_iff.mp hnot, map_zero, Finsupp.zero_apply]
    · have hrP := dichotomy P hP
      rw [ctrH_neg hP, AddMonoidHom.zero_apply, map_zero, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_eq_zero fun Q hQ => ?_
      have hQc := not_centred_of_rat Q (hrat i P hrP Q (Finsupp.mem_support_iff.mp hQ))
      rw [ctrH_neg hQc, AddMonoidHom.zero_apply]
  have hΦ : ∀ (i : ι) (D : Divisor E FE), Φ (TD i D) = TA i (Φ D) := by
    intro i
    suffices h : Φ.comp (TD i) = (TA i).comp Φ from fun D => DFunLike.congr_fun h D
    refine Finsupp.addHom_ext' fun P => AddMonoidHom.ext_int ?_
    simpa only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply] using key i P

  obtain ⟨Pη, hPη, -⟩ := hC1 η
  have hPηc : ∃ e : F →ₐ[K] E, Centred Pη e := ⟨η, hPη⟩

  obtain ⟨x, hx, -⟩ := id hfg
  obtain ⟨x₀, hx₀, hx₀fin⟩ := id hfgE
  haveI := hx₀fin
  have hxne : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hli : LinearIndependent K ![(1 : F), x] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx
      have ht' : algebraMap K F t ≠ 0 := (map_ne_zero _).2 ht
      have hx' : x = algebraMap K F (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff ht', mul_comm]
        exact eq_neg_of_add_eq_zero_right hst
      rw [hx']
      exact isAlgebraic_algebraMap _
  have hxE : algebraMap F FE x ∉ (algebraMap E FE).range := by
    have hli' := linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hli
    have h2 : LinearIndependent E ![algebraMap F FE 1, algebraMap F FE x] := by
      convert hli' using 1
      ext j
      fin_cases j <;> rfl
    rw [LinearIndependent.pair_iff] at h2
    rintro ⟨c, hc⟩
    have := h2 c (-1) (by rw [map_one, ← hc, Algebra.smul_def, mul_one, neg_one_smul, add_neg_cancel])
    exact absurd this.2 (by norm_num)
  have hcE' : ¬ ∀ v : Place E FE, v.ord (algebraMap F FE x) = 0 := fun h =>
    hxE (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x₀ hx₀ h)
  push Not at hcE'
  obtain ⟨cE, hcE⟩ := hcE'
  have hxEne : algebraMap F FE x ≠ 0 := (map_ne_zero _).2 hxne
  have hcErat : ∃ f : F, algebraMap F FE f ∉ cE.toValuationSubring := by
    rcases lt_or_gt_of_ne hcE with hlt | hgt
    · exact ⟨x, not_mem_of_ord_neg cE hxEne hlt⟩
    · refine ⟨x⁻¹, ?_⟩
      rw [map_inv₀]
      exact not_mem_of_ord_neg cE (inv_ne_zero hxEne) (by rw [Place.ord_inv]; omega)
  have hcEnc : ¬ ∃ e : F →ₐ[K] E, Centred cE e := not_centred_of_rat cE hcErat

  have hdeg1 : ∀ P : Place E FE, Divisor.degree (Finsupp.single P (1 : ℤ)) = 1 := fun P => by
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed P]; simp
  let D0 : Divisor.degZero (K := E) (F := FE) :=
    ⟨Finsupp.single Pη 1 - Finsupp.single cE 1, by
      rw [Divisor.mem_degZero, map_sub, hdeg1, hdeg1, sub_self]⟩
  have hΦD0 : Φ (D0 : Divisor E FE) = Finsupp.single η 1 := by
    show Φ (Finsupp.single Pη 1 - Finsupp.single cE 1) = Finsupp.single η 1
    rw [map_sub, hΦdef, Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single,
      ctrH_pos hPηc, ctrH_neg hcEnc, Centred.eq hPηc.choose_spec hPη,
      Finsupp.singleAddHom_apply, AddMonoidHom.zero_apply, sub_zero]

  have hmk := lift_equivariant
    (QuotientAddGroup.mk' ((Divisor.principal (K := E) (F := FE)).addSubgroupOf Divisor.degZero))
    TZ (fun i => Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i))
    (fun i D => rfl) p D0
  rw [hpE, LinearMap.zero_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal] at hmk
  obtain ⟨g, hg0, hdiv⟩ := hmk

  have hmain := lift_equivariant (Φ.comp (Divisor.degZero (K := E) (F := FE)).subtype) TZ TA
    (fun i D => hΦ i (D : Divisor E FE)) p D0
  simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply] at hmain
  rw [hΦD0] at hmain

  set Dg : Divisor E FE :=
    ((FreeAlgebra.lift ℤ (fun i => (TZ i).toIntLinearMap) p D0 :
      Divisor.degZero (K := E) (F := FE)) : Divisor E FE) with hDg
  have hDgv : ∀ v : Place E FE, Dg v = v.ord g := hdiv
  let y : Place E FE → (F →ₐ[K] E) := fun Q =>
    if h : ∃ e : F →ₐ[K] E, Centred Q e then h.choose else η
  refine ⟨g, hg0, Dg.support.filter (fun Q => ∃ e : F →ₐ[K] E, Centred Q e), y, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨-, hPc⟩ := Finset.mem_filter.mp hP
    show Centred P (y P)
    simp only [y, dif_pos hPc]
    exact hPc.choose_spec
  · intro P hPS hPg
    refine dichotomy P fun hPc => hPS ?_
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rwa [hDgv]), hPc⟩
  · rw [← hmain, hΦdef, Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Q _ => ?_
    by_cases hQc : ∃ e : F →ₐ[K] E, Centred Q e
    · rw [if_pos hQc, ctrH_pos hQc, Finsupp.singleAddHom_apply, hDgv]
      simp only [y, dif_pos hQc]
    · rw [if_neg hQc, ctrH_neg hQc, AddMonoidHom.zero_apply]

end S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero (solution)
