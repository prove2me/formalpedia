-- Prove2me | solution 1 for AlgebraicCurve.Place.subfieldClosure_range_union_eq_top_of_restrictAlong_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/54e1e6fa-6d9a-5b42-8aaf-2c9a05267f5b

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_subfieldClosure_range_union_eq_top_of_restrictAlong_injOn
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

universe u

open AlgebraicCurve
open scoped IntermediateField

namespace FFGEN

theorem ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F) {c : K} (hc : c ≠ 0) :
    P.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (⟨algebraMap K F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, P.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, P.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap K F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

theorem eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F) (x : F) {c c' : K}
    (hc : 0 < P.ord (x - algebraMap K F c)) (hc' : 0 < P.ord (x - algebraMap K F c')) : c = c' := by
  by_contra hne
  have h1 : x - algebraMap K F c ≠ 0 := by intro h; rw [h, Place.ord_zero] at hc; exact lt_irrefl _ hc
  have h2 : x - algebraMap K F c' ≠ 0 := by intro h; rw [h, Place.ord_zero] at hc'; exact lt_irrefl _ hc'
  have h3 : algebraMap K F (c' - c) ≠ 0 := (map_ne_zero _).2 (sub_ne_zero.2 (Ne.symm hne))
  have hsum : (x - algebraMap K F c) + (-(x - algebraMap K F c')) = algebraMap K F (c' - c) := by rw [map_sub]; ring
  have h4 : (x - algebraMap K F c) + (-(x - algebraMap K F c')) ≠ 0 := by rw [hsum]; exact h3
  have hmin := P.min_ord_le_ord_add h1 (neg_ne_zero.2 h2) h4
  rw [hsum] at hmin
  have hneg : ∀ f : F, P.ord (-f) = P.ord f := by
    intro f; rw [show -f = f * (-1) by ring]
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    · rw [P.ord_mul hf (by norm_num), show (-1 : F) = algebraMap K F (-1) by simp, ord_algebraMap P (by norm_num), add_zero]
  rw [hneg, ord_algebraMap P (sub_ne_zero.2 (Ne.symm hne))] at hmin
  have : min (P.ord (x - algebraMap K F c)) (P.ord (x - algebraMap K F c')) > 0 := lt_min hc hc'
  omega

end FFGEN

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {F F' : Type u} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [Field F'] [Algebra K F'] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ₀ φ₁ : F →ₐ[K] F') (h₀ : φ₀.toRingHom.IsIntegral) (h₁ : φ₁.toRingHom.IsIntegral)
    (hf₀ : FiniteAlong K φ₀) (hf₁ : FiniteAlong K φ₁)
    (S : Set (Place K F')) (hS : S.Finite)
    (hinj : ∀ P P' : Place K F', P ∉ S → P' ∉ S →
      P.restrictAlong φ₀ h₀ = P'.restrictAlong φ₀ h₀ → P.restrictAlong φ₁ h₁ = P'.restrictAlong φ₁ h₁ → P = P') :
    Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) = ⊤ := by
  classical

  set M : IntermediateField K F' := IntermediateField.adjoin K (Set.range φ₀ ∪ Set.range φ₁) with hMdef
  have hMS : M.toSubfield = Subfield.closure (Set.range φ₀ ∪ Set.range φ₁) := by
    rw [hMdef, IntermediateField.adjoin_toSubfield]
    apply le_antisymm
    · refine Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure)
      rintro _ ⟨c, rfl⟩
      exact Subfield.subset_closure (Set.mem_union_left _ ⟨algebraMap K F c, φ₀.commutes c⟩)
    · exact Subfield.closure_mono Set.subset_union_right
  suffices hMtop : M = ⊤ by
    rw [← hMS, hMtop]; ext y; simp

  obtain ⟨t₀, ht₀, -, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hφ₀inj : Function.Injective φ₀ := φ₀.toRingHom.injective
  have hx : Transcendental K (φ₀ t₀) := fun h => ht₀ ((isAlgebraic_algHom_iff φ₀ hφ₀inj).1 h)
  have hxM : φ₀ t₀ ∈ M := IntermediateField.subset_adjoin K _ (Set.mem_union_left _ ⟨t₀, rfl⟩)
  have hfdx : FiniteDimensional K⟮φ₀ t₀⟯ F' :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hx

  have hle : K⟮φ₀ t₀⟯ ≤ M := IntermediateField.adjoin_simple_le_iff.2 hxM
  haveI hMF'fin : Module.Finite M F' := by
    letI : Algebra K⟮φ₀ t₀⟯ M := (IntermediateField.inclusion hle).toAlgebra
    haveI : IsScalarTower K⟮φ₀ t₀⟯ M F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact Module.Finite.of_restrictScalars_finite K⟮φ₀ t₀⟯ M F'
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : Algebra.IsIntegral M F' := Algebra.IsIntegral.of_finite M F'
  haveI hsep : Algebra.IsSeparable M F' := Algebra.IsSeparable.of_integral M F'
  haveI : CharZero K⟮φ₀ t₀⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮φ₀ t₀⟯).injective
  haveI : Algebra.IsIntegral K⟮φ₀ t₀⟯ F' := Algebra.IsIntegral.of_finite _ F'
  have hsepx : Algebra.IsSeparable K⟮φ₀ t₀⟯ F' := Algebra.IsSeparable.of_integral _ F'

  by_contra hne
  have hd : 2 ≤ Module.finrank M F' := by
    have h1 : 0 < Module.finrank M F' := Module.finrank_pos
    by_contra hlt
    have h1' : Module.finrank M F' = 1 := by omega
    apply hne
    have hbt : (⊥ : Subalgebra M F') = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1'
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ (⊤ : Subalgebra M F') := Algebra.mem_top
    rw [← hbt, Algebra.mem_bot] at hy
    obtain ⟨m, rfl⟩ := hy
    exact m.2

  have hιint : (IsScalarTower.toAlgHom K M F').toRingHom.IsIntegral := fun y => Algebra.IsIntegral.isIntegral (R := M) y
  have hFI : FundamentalIdentity K M F' :=
    AlgebraicCurve.fundamentalIdentityAlong (IsScalarTower.toAlgHom K M F') hιint hMF'fin hsep
  have hdegF' : ∀ w : Place K F', w.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdegM : ∀ w : Place K F', (w.restrict M).deg = 1 := by
    intro w
    have h := w.deg_restrict_mul_inertiaDeg (F := M)
    rw [hdegF'] at h
    exact Nat.eq_one_of_mul_eq_one_right h
  have hcount : ∀ w₀ : Place K F', ∑ w ∈ (w₀.restrict M).fiber F', (w.ramificationIndex M : ℤ) = Module.finrank M F' := by
    intro w₀
    have h := hFI.sum_ramificationIndex_mul_deg (w₀.restrict M)
    simp only [hdegF', hdegM, Nat.cast_one, mul_one] at h
    exact h

  have hres : ∀ (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hφM : Set.range φ ⊆ M) (w w' : Place K F'),
      w.restrict M = w'.restrict M → w.restrictAlong φ hφ = w'.restrictAlong φ hφ := by
    intro φ hφ hφM w w' hww'
    apply Place.ext
    ext f
    have key : ∀ w₀ : Place K F', f ∈ (w₀.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w₀.toValuationSubring := by
      intro w₀; rfl
    have key2 : ∀ w₀ : Place K F', φ f ∈ w₀.toValuationSubring ↔
        (⟨φ f, hφM ⟨f, rfl⟩⟩ : M) ∈ (w₀.restrict M).toValuationSubring := by
      intro w₀; rfl
    rw [key, key, key2, key2, hww']

  obtain ⟨C, hC⟩ := AlgebraicCurve.Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos (K := K) (F := F')
    (φ₀ t₀) hx hfdx hsepx

  have hSfin := hS
  let bad : Place K F' → Set K := fun w => {c | 0 < w.ord (φ₀ t₀ - algebraMap K F' c)}
  have hbad1 : ∀ w, (bad w).Subsingleton := fun w c hc c' hc' => FFGEN.eq_of_ord_sub_pos w (φ₀ t₀) hc hc'
  have hbadfin : (⋃ w ∈ S, bad w).Finite := Set.Finite.biUnion hS (fun w _ => (hbad1 w).finite)
  have hfinbad : ((↑C : Set K) ∪ ⋃ w ∈ S, bad w).Finite := C.finite_toSet.union hbadfin
  obtain ⟨c, hc⟩ := hfinbad.infinite_compl.nonempty
  have hcC : c ∉ C := fun h => hc (Or.inl h)
  have hcS : ∀ w ∈ S, ¬ 0 < w.ord (φ₀ t₀ - algebraMap K F' c) := fun w hw h => hc (Or.inr (Set.mem_biUnion hw h))

  have hy0 : φ₀ t₀ - algebraMap K F' c ≠ 0 := by
    intro h
    exact hx (sub_eq_zero.1 h ▸ isAlgebraic_algebraMap c)
  obtain ⟨vinf, hvinf⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental (K := K) (φ₀ t₀) hx
  have hpole : vinf.ord (φ₀ t₀ - algebraMap K F' c) < 0 := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simpa using hvinf
    · have : vinf.ord (φ₀ t₀) < vinf.ord (-(algebraMap K F' c)) := by
        rw [show -(algebraMap K F' c) = algebraMap K F' (-c) by simp, FFGEN.ord_algebraMap vinf (neg_ne_zero.2 hc0)]
        exact hvinf
      have hx0 : φ₀ t₀ ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
      rw [sub_eq_add_neg, vinf.ord_add_eq_of_lt hx0 (by simpa using hc0) this]
      exact hvinf
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : Place K F', 0 < w₁.ord (φ₀ t₀ - algebraMap K F' c) := by
    obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (φ₀ t₀ - algebraMap K F' c) hy0
    by_contra hall
    push Not at hall

    have hdeg' : Divisor.degree D = D.sum (fun v n => n * (v.deg : ℤ)) := Finsupp.liftAddHom_apply _ _
    rw [hdeg'] at hdeg
    have hsupp : vinf ∈ D.support := by rw [Finsupp.mem_support_iff, hD]; exact ne_of_lt hpole
    unfold Finsupp.sum at hdeg
    rw [← Finset.add_sum_erase _ _ hsupp] at hdeg
    have h1 : D vinf * (vinf.deg : ℤ) < 0 := by rw [hdegF', Nat.cast_one, mul_one, hD]; exact hpole
    have h2 : ∑ v ∈ D.support.erase vinf, D v * (v.deg : ℤ) ≤ 0 := by
      apply Finset.sum_nonpos
      intro v _
      rw [hdegF', Nat.cast_one, mul_one, hD]
      exact hall v
    have h3 : D vinf * (vinf.deg : ℤ) + ∑ v ∈ D.support.erase vinf, D v * (v.deg : ℤ) = 0 := hdeg
    omega
  have hw₁1 : w₁.ord (φ₀ t₀ - algebraMap K F' c) = 1 := hC c hcC w₁ hw₁

  have hyM : φ₀ t₀ - algebraMap K F' c ∈ M := M.sub_mem hxM (M.algebraMap_mem c)
  set yM : M := ⟨φ₀ t₀ - algebraMap K F' c, hyM⟩ with hyMdef
  have hyM' : algebraMap M F' yM = φ₀ t₀ - algebraMap K F' c := rfl
  set u : Place K M := w₁.restrict M with hudef
  have hu : 0 < u.ord yM ∧ ∀ w : Place K F', w.restrict M = u →
      w.ord (φ₀ t₀ - algebraMap K F' c) = 1 ∧ w.ramificationIndex M = 1 := by
    have e1 := w₁.ord_restrict (F := M) yM
    rw [hyM', hw₁1, ← hudef] at e1
    have hepos := w₁.ramificationIndex_pos (F := M)
    have hord : u.ord yM = 1 ∧ (w₁.ramificationIndex M : ℤ) = 1 := by
      have hnn : 0 ≤ u.ord yM := by
        by_contra hneg; push Not at hneg
        have : (w₁.ramificationIndex M : ℤ) * u.ord yM < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hepos) hneg
        omega
      have he1 : (w₁.ramificationIndex M : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hepos.le) e1.symm
      have hord1 : u.ord yM = 1 := by rw [he1, one_mul] at e1; exact e1.symm
      exact ⟨hord1, he1⟩
    refine ⟨by rw [hord.1]; exact one_pos, fun w hw => ?_⟩
    have e2 := w.ord_restrict (F := M) yM
    rw [hyM', hw, hord.1, mul_one] at e2
    have hwpos : 0 < w.ord (φ₀ t₀ - algebraMap K F' c) := by rw [e2]; exact_mod_cast w.ramificationIndex_pos (F := M)
    have hw1 := hC c hcC w hwpos
    exact ⟨hw1, by exact_mod_cast (e2.symm.trans hw1)⟩

  have hcard : ((u.fiber F').card : ℤ) = Module.finrank M F' := by
    rw [hudef, ← hcount w₁, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [(hu.2 w (Place.mem_fiber.1 hw)).2]
  have hcard2 : 1 < (u.fiber F').card := by omega
  obtain ⟨w₂, hw₂, w₃, hw₃, hne23⟩ := Finset.one_lt_card.1 hcard2
  have hw₂u := Place.mem_fiber.1 hw₂
  have hw₃u := Place.mem_fiber.1 hw₃
  have hw₂S : w₂ ∉ S := fun h => hcS w₂ h (by rw [(hu.2 w₂ hw₂u).1]; exact one_pos)
  have hw₃S : w₃ ∉ S := fun h => hcS w₃ h (by rw [(hu.2 w₃ hw₃u).1]; exact one_pos)
  have h0M : Set.range φ₀ ⊆ (M : Set F') := fun z hz => IntermediateField.subset_adjoin K _ (Set.mem_union_left _ hz)
  have h1M : Set.range φ₁ ⊆ (M : Set F') := fun z hz => IntermediateField.subset_adjoin K _ (Set.mem_union_right _ hz)
  exact hne23 (hinj w₂ w₃ hw₂S hw₃S (hres φ₀ h₀ h0M w₂ w₃ (hw₂u.trans hw₃u.symm)) (hres φ₁ h₁ h1M w₂ w₃ (hw₂u.trans hw₃u.symm)))

end S_AlgebraicCurve_Place_subfieldClosure_range_union_eq_top_of_restrictAlong_injOn
end P2MW
export P2MW.S_AlgebraicCurve_Place_subfieldClosure_range_union_eq_top_of_restrictAlong_injOn (solution)
