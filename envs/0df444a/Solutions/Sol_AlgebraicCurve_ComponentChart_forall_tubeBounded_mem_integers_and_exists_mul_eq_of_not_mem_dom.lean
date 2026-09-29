-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.forall_tubeBounded_mem_integers_and_exists_mul_eq_of_not_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b3909621-0e86-5f00-87e3-c4f5e6ec35ec

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_forall_tubeBounded_mem_integers_and_exists_mul_eq_of_not_mem_dom
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace WAff1

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pos_of_residue_eq_zero {f : F} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring)
    (h : residue ↥v.toValuationSubring ⟨f, hf⟩ = 0) : 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hf
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    rw [IsLocalRing.residue_eq_zero_iff] at h
    have hunit : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
      have : (⟨f, hf⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := by
        apply Subtype.ext
        show f = _
        rw [hu, ← heq, zpow_zero, mul_one]
      rw [this]; exact Units.isUnit u
    exact (IsLocalRing.mem_maximalIdeal _).mp h hunit

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have h2 : algebraMap K F c⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' c⁻¹
  have hu : IsUnit (⟨algebraMap K F c, h1⟩ : v.toValuationSubring) := by
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show algebraMap K F c * algebraMap K F c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    · apply Subtype.ext
      show algebraMap K F c⁻¹ * algebraMap K F c = 1
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  obtain ⟨w, hw⟩ := hu
  have := v.ord_coe_unit w
  rwa [hw] at this

theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_prod {ι : Type*} (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem finite_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    {v : Place K F | v.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
  refine (D.support.finite_toSet).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  exact hw

theorem evalAt_zero : v.evalAt (0 : F) = 0 := by
  have := AlgebraicCurve.Place.evalAt_algebraMap v (0 : K)
  rwa [map_zero] at this

end PlaceFacts

end WAff1

open WAff1

theorem solution {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [IsAlgClosed L] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (C : ComponentChart A F Fbar)
    (hrat : ∀ P ∈ C.dom, P.IsRational)
    (hfib : {Q : Place (ResidueField A) Fbar | ∃ P ∈ C.dom, C.placeMap P = Q}.Infinite)
    (Pinf : Place L F) (hPinf : Pinf ∉ C.dom) :
    (∀ f : F, C.tubeBounded f → f ∈ C.integers) ∧
    ∀ h : F, h ∈ C.integers → ∃ (r s : F) (hs : s ∈ C.integers),
      C.tubeBounded r ∧ C.tubeBounded s ∧ C.residue ⟨s, hs⟩ ≠ 0 ∧ h * s = r := by
  classical

  have hdomInf : C.dom.Infinite := by
    intro hfin
    apply hfib
    have : {Q : Place (ResidueField A) Fbar | ∃ P ∈ C.dom, C.placeMap P = Q} = C.placeMap '' C.dom := by
      ext Q; simp [Set.mem_image]
    rw [this]
    exact hfin.image _

  have tb_of_regular : ∀ (g : F) (hg : g ∈ C.integers), (∀ P ∈ C.dom, g ∈ P.toValuationSubring) →
      C.tubeBounded g := by
    intro g hg hreg P hP
    refine ⟨hreg P hP, ?_⟩
    obtain ⟨-, h, -⟩ := C.pointwise P hP (hrat P hP) g hg (fun w hw _ => hreg w hw)
    exact h
  refine ⟨?_, ?_⟩

  · intro f hf
    by_contra hnot
    have hf0 : f ≠ 0 := fun h => hnot (h ▸ C.integers.zero_mem)
    obtain ⟨c, hc, hres⟩ := C.exists_smul_mem f hf0
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hres
      have : (⟨(0 : L) • f, hc⟩ : ↥C.integers) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]

    have hfinv : f⁻¹ ∈ C.integers := (C.integers.mem_or_inv_mem f).resolve_left hnot
    have hcF : algebraMap L F c ∈ C.integers := by
      have : algebraMap L F c = (c • f) * f⁻¹ := by
        rw [Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hf0, mul_one]
      rw [this]; exact mul_mem hc hfinv
    have hcA : c ∈ A := (C.algebraMap_mem_iff c).mp hcF
    have hcmax : (⟨c, hcA⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hnot
      obtain ⟨⟨a, b, hab, hba⟩, hau⟩ := hu
      change a = ⟨c, hcA⟩ at hau
      rw [hau] at hab
      have hinv : c⁻¹ ∈ A := by
        have h1 : c * (b : L) = 1 := by simpa using congrArg Subtype.val hab
        rw [inv_eq_of_mul_eq_one_right h1]; exact b.2
      have : f = c⁻¹ • (c • f) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, Algebra.smul_def]
      exact mul_mem ((C.algebraMap_mem_iff _).mpr hinv) hc

    set g : F := c • f with hg_def
    have hg0 : g ≠ 0 := smul_ne_zero hc0 hf0
    have hvan : ∀ P ∈ C.dom, 0 < (C.placeMap P).ord (C.residue ⟨g, hc⟩) := by
      intro P hP
      have hPr := hrat P hP
      have hfP : f ∈ P.toValuationSubring := (hf P hP).1
      have hcP : algebraMap L F c ∈ P.toValuationSubring := P.algebraMap_mem' c
      have hgw : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → g ∈ w.toValuationSubring := by
        intro w hw _
        rw [hg_def, Algebra.smul_def]
        exact mul_mem (w.algebraMap_mem' c) (hf w hw).1
      obtain ⟨hm, h, heq⟩ := C.pointwise P hP hPr g hc hgw
      have hval : P.evalAt g = c * P.evalAt f := by
        rw [hg_def, Algebra.smul_def, AlgebraicCurve.Place.evalAt_mul P hPr hcP hfP,
          AlgebraicCurve.Place.evalAt_algebraMap]
      have hmax : (⟨P.evalAt g, h⟩ : ↥A) ∈ maximalIdeal ↥A := by
        have : (⟨P.evalAt g, h⟩ : ↥A) = ⟨c, hcA⟩ * ⟨P.evalAt f, (hf P hP).2⟩ :=
          Subtype.ext (by simpa using hval)
        rw [this]
        exact Ideal.mul_mem_right _ _ hcmax
      have hres0 : residue ↥(C.placeMap P).toValuationSubring ⟨C.residue ⟨g, hc⟩, hm⟩ = 0 := by
        rw [← heq, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, map_zero]
      exact ord_pos_of_residue_eq_zero (C.placeMap P) hres hm hres0

    obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) g hg0
    let D : Divisor L F := D₀.filter (fun P => P ∈ C.dom)
    have hD1 : ∀ P ∈ C.dom, D P = P.ord g := by
      intro P hP; simp only [D, Finsupp.filter_apply, if_pos hP, hD₀ P]
    have hD2 : ∀ P, P ∉ C.dom → D P = 0 := by
      intro P hP; simp only [D, Finsupp.filter_apply, if_neg hP]
    have hpush := C.mapDomain_placeMap ⟨g, hc⟩ hres D hD1 hD2
    apply hfib
    refine ((Finsupp.mapDomain C.placeMap D).support.finite_toSet).subset ?_
    rintro Q ⟨P, hP, rfl⟩
    have hQ : C.placeMap P ∉ C.nodes := C.placeMap_not_mem_nodes P hP
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, hpush _ hQ]
    exact (hvan P hP).ne'

  · intro h hh
    rcases eq_or_ne h 0 with rfl | hh0
    · refine ⟨0, 1, C.integers.one_mem, ?_, ?_, ?_, by ring⟩
      · intro P hP; exact ⟨zero_mem _, by rw [evalAt_zero]; exact zero_mem _⟩
      · intro P hP; exact ⟨one_mem _, by rw [Place.evalAt_one]; exact one_mem _⟩
      · have : (⟨(1 : F), C.integers.one_mem⟩ : ↥C.integers) = 1 := rfl
        rw [this, map_one]; exact one_ne_zero

    have hG : ∀ P : Place L F, ∃ gP : F, gP ≠ 0 ∧ (∀ v : Place L F, v ≠ Pinf → 0 ≤ v.ord gP) ∧
        (P ∈ C.dom → 0 < P.ord gP) := by
      intro P
      by_cases hP : P ∈ C.dom
      · obtain ⟨P', hP', hP'ne⟩ := (hdomInf.diff (Set.finite_singleton P)).nonempty
        have hPne : P ≠ Pinf := fun e => hPinf (e ▸ hP)
        have hP'ne' : P' ≠ Pinf := fun e => hPinf (e ▸ hP')
        have hPP' : P ≠ P' := fun e => hP'ne (by simp [e])
        obtain ⟨gP, hmem, hpos, -⟩ :=
          AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero L F Pinf P P'
            hPne hP'ne' hPP'
        have hgP0 : gP ≠ 0 := by rintro rfl; simp at hpos
        refine ⟨gP, hgP0, ?_, fun _ => hpos⟩
        intro v hv
        rcases (mem_riemannRochSpace_iff.mp hmem) v with h0 | hle
        · exact absurd h0 hgP0
        · simpa [Finsupp.smul_apply, Finsupp.single_apply, hv.symm, Ne.symm hv] using hle
      · exact ⟨1, one_ne_zero, fun v _ => by simp, fun h => absurd h hP⟩
    choose G hG0 hGreg hGpos using hG

    obtain ⟨Dh, hDh, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) h hh0
    let T : Finset (Place L F) := Dh.support.filter (fun P => P ∈ C.dom ∧ Dh P < 0)
    have hT : ∀ P, P ∈ T ↔ P ∈ C.dom ∧ P.ord h < 0 := by
      intro P
      simp only [T, Finset.mem_filter, Finsupp.mem_support_iff, hDh P]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2.ne, h1, h2⟩

    let n : Place L F → ℕ := fun P => (P.ord h).natAbs
    let f : F := ∏ P ∈ T, G P ^ n P
    have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (hG0 P)
    have hford : ∀ v : Place L F, v.ord f = ∑ P ∈ T, (n P : ℤ) * v.ord (G P) := by
      intro v
      rw [ord_prod v T _ (fun P _ => pow_ne_zero _ (hG0 P))]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [ord_pow]
    have hfreg : ∀ v : Place L F, v ≠ Pinf → 0 ≤ v.ord f := by
      intro v hv
      rw [hford]
      exact Finset.sum_nonneg fun P _ => mul_nonneg (Int.natCast_nonneg _) (hGreg P v hv)
    have hfzero : ∀ P ∈ T, -P.ord h ≤ P.ord f := by
      intro P hPT
      have hP : P ∈ C.dom := ((hT P).mp hPT).1
      have hneg : P.ord h < 0 := ((hT P).mp hPT).2
      have hPne : P ≠ Pinf := fun e => hPinf (e ▸ hP)
      rw [hford]
      calc -P.ord h = (n P : ℤ) * 1 := by simp only [n, mul_one]; omega
        _ ≤ (n P : ℤ) * P.ord (G P) :=
          mul_le_mul_of_nonneg_left (hGpos P hP) (Int.natCast_nonneg _)
        _ ≤ ∑ P' ∈ T, (n P' : ℤ) * P.ord (G P') :=
          Finset.single_le_sum (fun P' _ => mul_nonneg (Int.natCast_nonneg _) (hGreg P' P hPne)) hPT

    obtain ⟨c, hcs, hsres⟩ := C.exists_smul_mem f hf0
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hsres
      have : (⟨(0 : L) • f, hcs⟩ : ↥C.integers) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]
    set s : F := c • f with hs_def
    have hs0 : s ≠ 0 := smul_ne_zero hc0 hf0
    have hsord : ∀ v : Place L F, v.ord s = v.ord f := by
      intro v
      rw [hs_def, Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc0) hf0, ord_algebraMap v hc0,
        zero_add]
    have hsreg : ∀ P ∈ C.dom, s ∈ P.toValuationSubring := by
      intro P hP
      exact mem_of_ord_nonneg P hs0 ((hsord P).symm ▸ hfreg P (fun e => hPinf (e ▸ hP)))
    have hs_tb : C.tubeBounded s := tb_of_regular s hcs hsreg

    have hr : h * s ∈ C.integers := mul_mem hh hcs
    have hrreg : ∀ P ∈ C.dom, h * s ∈ P.toValuationSubring := by
      intro P hP
      apply mem_of_ord_nonneg P (mul_ne_zero hh0 hs0)
      rw [P.ord_mul hh0 hs0, hsord]
      by_cases hneg : P.ord h < 0
      · have := hfzero P ((hT P).mpr ⟨hP, hneg⟩); omega
      · have := hfreg P (fun e => hPinf (e ▸ hP)); omega
    exact ⟨h * s, s, hcs, tb_of_regular _ hr hrreg, hs_tb, hsres, rfl⟩

end S_AlgebraicCurve_ComponentChart_forall_tubeBounded_mem_integers_and_exists_mul_eq_of_not_mem_dom
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_forall_tubeBounded_mem_integers_and_exists_mul_eq_of_not_mem_dom (solution)
