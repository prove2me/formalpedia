-- Prove2me | solution 1 for AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/22db2db5-e600-523e-a59d-eff256bd76f2

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
import Theorems.Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub
import Theorems.Thm_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
import Theorems.Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_Place_evalAt_trace_eq_sum_fiber
import Theorems.Thm_AlgebraicCurve_Place_continuous_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead
import Theorems.Thm_Complex_circleIntegral_div_sub_eq_sum_div_deriv
import Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FiniteAlong Divisor.correspondence Divisor.correspondence_apply Place.ord_restrictAlong Divisor.pushforwardAlong_single Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single SeparableAlong Place.restrictInclusion Place.restrictResidueMap_residue Place.algebraMap_residueField_eq Place Place.FiniteResidue Place.ord_zero Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.algebraMap_mem' Differential.pullbackAlong Differential.pullbackAlong_D Differential.traceAlong_smul_pullbackAlong Differential.correspondence Differential.correspondence_apply IsCurveOver IsCurveOver.finrank_kaehler IsCurveOver.instNontrivialKaehler IsCurveOver.deg_eq_one_of_isAlgClosed Place.evalAt regularDifferentials mem_regularDifferentials_iff Place.chartRead_apply Place.readDifferential_apply abelJacobiVec abelJacobiDiv abelJacobiDiv_single pathPeriodLattice Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex isCurveOver_of_transcendental separableAlong_of_charZero Differential.correspondence_mem_regularDifferentials Place.evalAt_trace_eq_sum_fiber Place.continuous_restrictAlong Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice Place.restrictAlong_surjective Place.D_ne_zero_of_ord_ne_zero"
namespace HurwitzLocalProof
p2m_open "AlgebraicCurve"

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] (f : F) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  by_cases hf0 : f = 0
  · subst hf0
    convert Set.finite_empty
    ext w
    simp
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf0 : f ≠ 0) :
    {w : Place K F | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h : w.ord f ≠ 0 := hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_zero (w : Place K F) : w.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap w (0 : K)

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v h.le
  have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    change v.ord f = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (mem_nonunits_iff.2 hnu))
  rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem ord_algebraMap (v : Place K F) (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hu : IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
      refine IsUnit.of_mul_eq_one ⟨algebraMap K F a⁻¹, v.algebraMap_mem' a⁻¹⟩ ?_
      ext
      simp [ha]
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this

theorem differentialCoeff_mem (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {η : Ω[F⁄K]} (hη : η ∈ regularDifferentials K F) :
    v.differentialCoeff η ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfe⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hη v
  rwa [v.differentialCoeff_unique hfe]

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [v.ord_dCoordFn]; exact zero_le_one)

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h
  have := v.ord_dCoordFn
  rw [h, v.ord_zero] at this
  exact zero_ne_one this

end Algebra

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (f : F) : f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < w.ramificationIndexAlong φ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem evalAt_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.IsRational) (hv : (w.restrictAlong φ hφ).IsRational) (f : F) :
    (w.restrictAlong φ hφ).evalAt f = w.evalAt (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  change (w.restrict F).evalAt f = w.evalAt (algebraMap F F' f)
  by_cases hf : f ∈ (w.restrict F).toValuationSubring
  · have hf' : algebraMap F F' f ∈ w.toValuationSubring := hf
    apply w.algebraMap_residueField_injective
    rw [w.algebraMap_evalAt hw hf']
    have h1 : (⟨algebraMap F F' f, hf'⟩ : w.toValuationSubring) =
        Place.restrictInclusion F w ⟨f, hf⟩ := rfl
    rw [h1, ← Place.restrictResidueMap_residue, ← (w.restrict F).algebraMap_evalAt hv hf,
      ← Place.algebraMap_residueField_eq, ← IsScalarTower.algebraMap_apply]
  · have hf' : algebraMap F F' f ∉ w.toValuationSubring := hf
    rw [Place.evalAt, dif_neg hf, Place.evalAt, dif_neg hf']

theorem inertiaDegAlong_eq_one [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong ψ hψ = 1 := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem correspondence_single [HasPrincipalDivisors K F'] [IsAlgClosed K] [IsCurveOver K F]
    [IsCurveOver K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (Q : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single Q 1) =
      ∑ W ∈ Place.fiberAlong φ hφ Q,
        Finsupp.single (W.restrictAlong ψ hψ) (W.ramificationIndexAlong φ : ℤ) := by
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one ψ hψ W]
  simp

end Along

theorem isOpen_setOf_mem {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [T2Space (Place ℂ F)] (f : F) :
    IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
  have h : {w : Place ℂ F | f ∈ w.toValuationSubring} =
      {w : Place ℂ F | f ∉ w.toValuationSubring}ᶜ := by
    ext w; simp
  rw [h]
  exact (finite_setOf_not_mem (K := ℂ) f).isClosed.isOpen_compl

section Charts

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem symm_ne_center (v : Place ℂ F) {u : ℂ} (hu : u ∈ (extChartAt 𝓘(ℂ, ℂ) v).target)
    (hne : u ≠ extChartAt 𝓘(ℂ, ℂ) v v) : (extChartAt 𝓘(ℂ, ℂ) v).symm u ≠ v := by
  intro h
  apply hne
  calc u = extChartAt 𝓘(ℂ, ℂ) v ((extChartAt 𝓘(ℂ, ℂ) v).symm u) :=
        ((extChartAt 𝓘(ℂ, ℂ) v).right_inv hu).symm
    _ = extChartAt 𝓘(ℂ, ℂ) v v := by rw [h]

theorem eventually_symm_notMem [T2Space (Place ℂ F)] (v : Place ℂ F) (S : Set (Place ℂ F))
    (hS : S.Finite) :
    ∀ᶠ u in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v), (extChartAt 𝓘(ℂ, ℂ) v).symm u ∉ S := by
  have h1 : ∀ᶠ u in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), (extChartAt 𝓘(ℂ, ℂ) v).symm u ∉ S \ {v} := by
    have hcl : IsClosed (S \ {v}) := (hS.subset Set.diff_subset).isClosed
    have hmem : (S \ {v})ᶜ ∈ 𝓝 ((extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v)) := by
      rw [extChartAt_to_inv]
      exact hcl.isOpen_compl.mem_nhds (fun h => h.2 rfl)
    exact (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) v).preimage_mem_nhds hmem
  have h2 : ∀ᶠ u in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), u ∈ (extChartAt 𝓘(ℂ, ℂ) v).target :=
    extChartAt_target_mem_nhds v
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2] with u hu1 hu2 hne hS'
  exact hu1 ⟨hS', symm_ne_center v hu2 hne⟩

end Charts

section Compatible

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
    [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

theorem chartRead_center (P : Place ℂ F) (f : F) :
    P.chartRead f (extChartAt 𝓘(ℂ, ℂ) P P) = P.evalAt f := by
  rw [Place.chartRead_apply, extChartAt_to_inv]

variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

theorem enat_map_eq_coe {o : ℕ∞} {k : ℤ} (h : o.map (fun n : ℕ => (n : ℤ)) = (k : WithTop ℤ)) :
    o ≠ ⊤ ∧ ((o.toNat : ℕ) : ℤ) = k := by
  induction o using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    simp only [ENat.map_coe, WithTop.coe_eq_coe] at h
    exact ⟨ENat.coe_ne_top m, by simpa using h⟩

theorem analyticOrderAt_chartRead_sub (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (hf : f ∈ w.toValuationSubring) (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    (analyticOrderAt (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w)).map
        (fun n : ℕ => (n : ℤ)) = ((w.ord (f - algebraMap ℂ F t) : ℤ) : WithTop ℤ) := by
  obtain ⟨-, hord⟩ := hF (f - algebraMap ℂ F t) hne w
  have hreg : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) w).symm z).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds
      (t := {w' : Place ℂ F | f ∈ w'.toValuationSubring})
      (by rw [extChartAt_to_inv]; exact (isOpen_setOf_mem f).mem_nhds hf)
    exact this
  have hEq : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) (f - algebraMap ℂ F t))
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)] fun z => w.chartRead f z - t := by
    filter_upwards [hreg] with z hz
    rw [Place.chartRead_apply, sub_eq_add_neg, ← map_neg,
      evalAt_add _ (isRational _) hz (Place.algebraMap_mem' _ _), evalAt_algebraMap]
    ring
  rw [meromorphicOrderAt_congr (hEq.filter_mono nhdsWithin_le_nhds)] at hord
  have hA : AnalyticAt ℂ (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w) :=
    (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf).sub analyticAt_const
  rw [hA.meromorphicOrderAt_eq] at hord
  exact hord

theorem not_eventually_deriv_chartRead_eq_zero (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (hf : f ∈ w.toValuationSubring) (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) :
    ¬ ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) w w), deriv (w.chartRead f) z = 0 := by
  intro hd
  set c := extChartAt 𝓘(ℂ, ℂ) w w with hc
  set R := w.chartRead f with hR
  have hA : AnalyticAt ℂ R c :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf
  have hdc : deriv R c = 0 := by
    have hcont : ContinuousAt (deriv R) c := hA.deriv.continuousAt
    have h1 : Filter.Tendsto (deriv R) (𝓝[≠] c) (𝓝 (deriv R c)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (deriv R) (𝓝[≠] c) (𝓝 0) :=
      tendsto_const_nhds.congr' (hd.mono fun z hz => hz.symm)
    exact tendsto_nhds_unique h1 h2
  have hd' : ∀ᶠ z in 𝓝 c, deriv R z = 0 := by
    have := eventually_nhdsWithin_iff.1 hd
    filter_upwards [this] with z hz
    by_cases hzc : z = c
    · rw [hzc]; exact hdc
    · exact hz hzc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hd'.and hA.eventually_analyticAt)
  have hconst : ∀ z ∈ Metric.ball c ε, R z = R c := by
    intro z hz
    refine IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball c ε).isPreconnected
      (fun y hy => (hball y hy).2.differentiableAt.differentiableWithinAt)
      (fun y hy => (hball y hy).1) hz (Metric.mem_ball_self hε)
  have htop : analyticOrderAt (fun z => R z - R c) c = ⊤ := by
    rw [analyticOrderAt_eq_top]
    filter_upwards [Metric.ball_mem_nhds c hε] with z hz
    rw [hconst z hz, sub_self]
  have hne : f - algebraMap ℂ F (R c) ≠ 0 := fun h => hfc (R c) (sub_eq_zero.1 h)
  have hfin := analyticOrderAt_chartRead_sub hF w hf (R c) hne
  rw [htop] at hfin
  simp at hfin

theorem chartRead_dCoordFn (hF : ChartCompatible F) (v : Place ℂ F) :
    AnalyticAt ℂ (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      v.chartRead v.dCoordFn (extChartAt 𝓘(ℂ, ℂ) v v) = 0 ∧
      deriv (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) ≠ 0 := by
  have hA : AnalyticAt ℂ (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v (dCoordFn_mem v)
  have hval : v.chartRead v.dCoordFn (extChartAt 𝓘(ℂ, ℂ) v v) = 0 := by
    rw [chartRead_center]
    exact evalAt_eq_zero_of_ord_pos v (by rw [v.ord_dCoordFn]; exact one_pos)
  have hne : v.dCoordFn - algebraMap ℂ F 0 ≠ 0 := by
    rw [map_zero, sub_zero]; exact dCoordFn_ne_zero v
  have hord := analyticOrderAt_chartRead_sub hF v (dCoordFn_mem v) 0 hne
  rw [map_zero, sub_zero, v.ord_dCoordFn] at hord
  obtain ⟨htop, hk⟩ := enat_map_eq_coe hord
  have h1 : analyticOrderAt (fun z => v.chartRead v.dCoordFn z - 0) (extChartAt 𝓘(ℂ, ℂ) v v) =
      (1 : ℕ) := by
    rw [← ENat.coe_toNat htop]
    congr 1
    exact_mod_cast hk
  have hA0 : AnalyticAt ℂ (fun z => v.chartRead v.dCoordFn z - 0) (extChartAt 𝓘(ℂ, ℂ) v v) :=
    hA.sub analyticAt_const
  obtain ⟨q, hqa, hq0, hfac⟩ := hA0.analyticOrderAt_eq_natCast.1 h1
  set c := extChartAt 𝓘(ℂ, ℂ) v v with hc
  have hfun : (fun z => v.chartRead v.dCoordFn z - 0) =ᶠ[𝓝 c] fun z => (z - c) * q z :=
    hfac.mono fun z hz => by simpa only [pow_one, smul_eq_mul] using hz
  have hd : HasDerivAt (fun z => (z - c) * q z) (1 * q c + (c - c) * deriv q c) c :=
    ((hasDerivAt_id c).sub_const c).mul hqa.differentiableAt.hasDerivAt
  have h2 : deriv (fun z => v.chartRead v.dCoordFn z - 0) c = q c := by
    rw [hfun.deriv_eq, hd.deriv]; ring
  refine ⟨hA, hval, ?_⟩
  rw [show deriv (v.chartRead v.dCoordFn) c = deriv (fun z => v.chartRead v.dCoordFn z - 0) c by
    simp, h2]
  exact hq0

end Compatible

section Analysis

theorem eventually_forall_sphere_ne {R : ℂ → ℂ} {c t₀ : ℂ} {r : ℝ}
    (hcont : ContinuousOn R (Metric.sphere c r)) (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t₀) :
    ∀ᶠ t in 𝓝 t₀, ∀ z ∈ Metric.sphere c r, R z ≠ t := by
  rcases (Metric.sphere c r).eq_empty_or_nonempty with hemp | hnonempty
  · exact Filter.Eventually.of_forall fun t z hz => by simp [hemp] at hz
  have hc' : ContinuousOn (fun z => ‖R z - t₀‖) (Metric.sphere c r) :=
    (hcont.sub continuousOn_const).norm
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hnonempty hc'
  set δ := ‖R z₁ - t₀‖ with hδ
  have hδpos : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 (hne z₁ hz₁))
  filter_upwards [Metric.ball_mem_nhds t₀ hδpos] with t ht z hz hzt
  have hle : δ ≤ ‖R z - t₀‖ := isMinOn_iff.1 hmin z hz
  rw [hzt] at hle
  rw [Metric.mem_ball, dist_eq_norm] at ht
  linarith

theorem eq_of_eventually_eq_of_continuousAt {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℂ → E} {c : ℂ} (hf : ContinuousAt f c) (hg : ContinuousAt g c)
    (h : ∀ᶠ z in 𝓝[≠] c, f z = g z) : f c = g c := by
  have h1 : Filter.Tendsto f (𝓝[≠] c) (𝓝 (f c)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto g (𝓝[≠] c) (𝓝 (g c)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (h1.congr' h) h2

end Analysis

section Combinatorics

theorem sum_eq_sum_sum {α β γ M : Type*} [AddCommMonoid M]
    (S : Finset α) (Z₀ : Finset β) (Zf : β → Finset γ) (sy : β → γ → α)
    (hsurj : ∀ w ∈ S, ∃ v ∈ Z₀, ∃ a ∈ Zf v, sy v a = w)
    (hmem : ∀ v ∈ Z₀, ∀ a ∈ Zf v, sy v a ∈ S)
    (hinj : ∀ v ∈ Z₀, ∀ v' ∈ Z₀, ∀ a ∈ Zf v, ∀ a' ∈ Zf v', sy v a = sy v' a' → v = v' ∧ a = a')
    (cf : α → M) :
    ∑ w ∈ S, cf w = ∑ v ∈ Z₀, ∑ a ∈ Zf v, cf (sy v a) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => sy x.1 x.2) ?_ ?_ ?_ ?_
  · rintro ⟨v, a⟩ hx
    obtain ⟨hv, ha⟩ := Finset.mem_sigma.1 hx
    exact hmem v hv a ha
  · rintro ⟨v, a⟩ hx ⟨v', a'⟩ hx' h
    obtain ⟨hv, ha⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hv', ha'⟩ := Finset.mem_sigma.1 hx'
    obtain ⟨rfl, rfl⟩ := hinj v hv v' hv' a ha a' ha' h
    rfl
  · intro w hw
    obtain ⟨v, hv, a, ha, rfl⟩ := hsurj w hw
    exact ⟨⟨v, a⟩, Finset.mem_sigma.2 ⟨hv, ha⟩, rfl⟩
  · intros; rfl

end Combinatorics

section Roof

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem exists_finset_adjoin_eq_top
    (hfg : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F') :
    ∃ G : Finset F', IntermediateField.adjoin K (G : Set F') = ⊤ := by
  classical
  obtain ⟨x, -, hxfin⟩ := hfg
  set Kx := IntermediateField.adjoin K ({x} : Set F')
  haveI := hxfin
  let b := Module.finBasis Kx F'
  refine ⟨insert x (Finset.univ.image b), ?_⟩
  have hset : ((insert x (Finset.univ.image b) : Finset F') : Set F') = {x} ∪ Set.range b := by
    ext y
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range, Set.singleton_union]
  rw [hset, ← IntermediateField.adjoin_adjoin_left]
  have htop : IntermediateField.adjoin Kx (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hspan : f ∈ Submodule.span Kx (Set.range b) := by
      rw [b.span_eq]; trivial
    have hle : Submodule.span Kx (Set.range b) ≤
        (IntermediateField.adjoin Kx (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.2 (fun y hy => IntermediateField.subset_adjoin Kx _ hy)
    exact hle hspan
  rw [htop]
  rfl

theorem finiteAlong_of_isIntegral_of_adjoin_eq_top (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (T : Finset F')
    (hT : IntermediateField.adjoin K (T : Set F') = ⊤) : FiniteAlong K φ := by
  letI : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  have hT' : IntermediateField.adjoin F (T : Set F') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hle : IntermediateField.adjoin K (T : Set F') ≤
        (IntermediateField.adjoin F (T : Set F')).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have hy : y ∈ IntermediateField.adjoin K (T : Set F') := by rw [hT]; trivial
    exact hle hy
  haveI : FiniteDimensional F (IntermediateField.adjoin F (T : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun t _ => hφ t)
  have e : (IntermediateField.adjoin F (T : Set F')) ≃ₗ[F] F' :=
    ((IntermediateField.equivOfEq hT').trans IntermediateField.topEquiv).toLinearEquiv
  exact Module.Finite.equiv e

theorem roof_hfg_and_isCurveOver [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ) :
    (∃ y : F', Transcendental K y ∧
      FiniteDimensional (IntermediateField.adjoin K ({y} : Set F')) F') ∧ IsCurveOver K F' := by
  obtain ⟨x, hx, hxfin⟩ := hfg
  letI : Algebra F F' := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Module.Finite F F' := hfin
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx
  set y : F' := ψ x with hy_def
  set Ky : IntermediateField K F' := IntermediateField.adjoin K ({y} : Set F') with hKy
  have hy : Transcendental K y := fun h =>
    hx ((isAlgebraic_algHom_iff ψ ψ.toRingHom.injective).mp h)
  have hmap : ∀ z ∈ Kx, ψ z ∈ Ky := by
    intro z hz
    have hKxy : Kx.map ψ = Ky := by
      rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
    rw [← hKxy]
    exact ⟨z, hz, rfl⟩
  let f : Kx →+* Ky := ψ.toRingHom.restrict Kx Ky hmap
  letI algKxF' : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Kx F' := Module.Finite.trans F F'
  letI : Algebra Kx Ky := f.toAlgebra
  haveI : IsScalarTower Kx Ky F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfd : FiniteDimensional Ky F' := Module.Finite.of_restrictScalars_finite Kx Ky F'
  have hsep : Algebra.IsSeparable Ky F' := by
    haveI : FiniteDimensional Ky F' := hfd
    infer_instance
  exact ⟨⟨y, hy, hfd⟩, AlgebraicCurve.isCurveOver_of_transcendental hy hfd hsep⟩

end Roof

section LocalData

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
variable {F' : Type*} [Field F'] [Algebra ℂ F'] [IsCurveOver ℂ F']
variable [TopologicalSpace (Place ℂ F')] [ChartedSpace ℂ (Place ℂ F')] [T2Space (Place ℂ F')]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F')]

theorem local_data (hF : ChartCompatible F) (hF' : ChartCompatible F')
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F')) F')
    (hgen : ∀ v : Place ℂ F, v.DCoordGenerates)
    (φ ψ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F) (P₀ P : Place ℂ F)
    (g : Fin n → F')
    (hg : ∀ i, Differential.pullbackAlong ψ (b i) =
      g i • KaehlerDifferential.D ℂ F' (φ P.dCoordFn))
    (r₁ : ℝ) (hr₁ : 0 < r₁)
    (W : Place ℂ F') (hW : W.restrictAlong φ hφ = P)
    (O : Set (Place ℂ F')) (hO : IsOpen O) (hWO : W ∈ O) :
    ∃ ρ : ℝ, ∃ Ψ : Fin n → ℂ → ℂ, 0 < ρ ∧
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ ⊆ (extChartAt 𝓘(ℂ, ℂ) W).target ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ,
        (extChartAt 𝓘(ℂ, ℂ) W).symm u ∈ O ∧
          φ P.dCoordFn ∈ ((extChartAt 𝓘(ℂ, ℂ) W).symm u).toValuationSubring ∧
          ((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong φ hφ ∈ (extChartAt 𝓘(ℂ, ℂ) P).source ∧
          extChartAt 𝓘(ℂ, ℂ) P (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong φ hφ) ∈
            Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r₁) ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ,
        AnalyticAt ℂ (W.chartRead (φ P.dCoordFn)) u) ∧
      W.chartRead (φ P.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) W W) = 0 ∧
      (∀ i, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ, AnalyticAt ℂ (Ψ i) u) ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ,
        abelJacobiVec b P₀ (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong ψ hψ) -
            abelJacobiVec b P₀ (W.restrictAlong ψ hψ) -
            (fun i => Ψ i u - Ψ i (extChartAt 𝓘(ℂ, ℂ) W W)) ∈ pathPeriodLattice b) ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ, u ≠ extChartAt 𝓘(ℂ, ℂ) W W →
        W.chartRead (φ P.dCoordFn) u ≠ 0 ∧ deriv (W.chartRead (φ P.dCoordFn)) u ≠ 0 ∧
          (∀ i, g i ≠ 0 → ((extChartAt 𝓘(ℂ, ℂ) W).symm u).ord (g i) = 0) ∧
          ∀ i, HasDerivAt (Ψ i)
            (W.chartRead (g i) u * deriv (W.chartRead (φ P.dCoordFn)) u) u) := by
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  set π : F := P.dCoordFn with hπ
  set cW := extChartAt 𝓘(ℂ, ℂ) W W with hcW
  set σW := (extChartAt 𝓘(ℂ, ℂ) W).symm with hσW
  set pW : ℂ → ℂ := W.chartRead (φ π) with hpW
  have hrat : ∀ v : Place ℂ F, v.IsRational := fun v => isRational v
  have hrat' : ∀ w : Place ℂ F', w.IsRational := fun w => isRational w

  have hπP : π ∈ P.toValuationSubring := dCoordFn_mem P
  have hφπW : φ π ∈ W.toValuationSubring := by
    rw [← mem_restrictAlong_iff φ hφ, hW]; exact hπP
  have hordφπ : W.ord (φ π) = W.ramificationIndexAlong φ := by
    have := Place.ord_restrictAlong φ hφ W π
    rw [hW, P.ord_dCoordFn, mul_one] at this
    exact this
  have hepos : 0 < W.ramificationIndexAlong φ := ramificationIndexAlong_pos φ hφ W
  have hφπnc : ∀ a : ℂ, φ π ≠ algebraMap ℂ F' a := by
    intro a h
    have h0 := ord_algebraMap W a
    rw [← h, hordφπ] at h0
    omega
  have hφπne : φ π - algebraMap ℂ F' 0 ≠ 0 := by
    rw [map_zero, sub_zero]; exact fun h => hφπnc 0 (by rw [h, map_zero])
  have hpWc : pW cW = 0 := by
    rw [hpW, hcW, chartRead_center]
    exact evalAt_eq_zero_of_ord_pos W (by rw [hordφπ]; exact_mod_cast hepos)
  have hpWan : AnalyticAt ℂ pW cW :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F' hF' W hφπW

  obtain ⟨rA, hrA, htarA, Ψ, hΨd, hΨAJ⟩ :=
    AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice F hfg hF
      F' hfg' hF' ψ hψ b hb P₀ W
  have hΨan : ∀ i, ∀ u ∈ Metric.ball cW rA, AnalyticAt ℂ (Ψ i) u := by
    intro i u hu
    have hd : DifferentiableOn ℂ (Ψ i) (Metric.ball cW rA) := fun y hy =>
      (hΨd i y hy).differentiableAt.differentiableWithinAt
    exact hd.analyticAt (Metric.isOpen_ball.mem_nhds hu)

  have hcontφ : Continuous fun w : Place ℂ F' => w.restrictAlong φ hφ :=
    AlgebraicCurve.Place.continuous_restrictAlong F F' hF hF' φ hφ
  set Qφ : ℂ → Place ℂ F := fun u => (σW u).restrictAlong φ hφ with hQφ
  have hσWc : σW cW = W := by rw [hσW, hcW, extChartAt_to_inv]
  have hQφc : Qφ cW = P := by simp only [hQφ, hσWc, hW]
  have hQφcont : ContinuousAt Qφ cW :=
    hcontφ.continuousAt.comp (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) W)

  have e1 : ∀ᶠ u in 𝓝 cW, u ∈ Metric.ball cW rA := Metric.ball_mem_nhds cW hrA
  have e2 : ∀ᶠ u in 𝓝 cW, σW u ∈ O ∧ φ π ∈ (σW u).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) W).preimage_mem_nhds
      (t := O ∩ {w' : Place ℂ F' | φ π ∈ w'.toValuationSubring})
      (by
        rw [extChartAt_to_inv]
        exact (hO.inter (isOpen_setOf_mem (φ π))).mem_nhds ⟨hWO, hφπW⟩)
    exact this
  have e3 : ∀ᶠ u in 𝓝 cW, Qφ u ∈ (extChartAt 𝓘(ℂ, ℂ) P).source ∩
      extChartAt 𝓘(ℂ, ℂ) P ⁻¹' Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r₁ := by
    refine hQφcont.preimage_mem_nhds ?_
    rw [hQφc]
    exact (isOpen_extChartAt_preimage' (I := 𝓘(ℂ, ℂ)) P Metric.isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) P, Metric.mem_ball_self hr₁⟩
  have e9 : ∀ᶠ u in 𝓝 cW, AnalyticAt ℂ pW u := hpWan.eventually_analyticAt

  have hordfin : analyticOrderAt (fun z => pW z - 0) cW ≠ ⊤ :=
    (enat_map_eq_coe (analyticOrderAt_chartRead_sub hF' W hφπW 0 hφπne)).1
  have p1 : ∀ᶠ u in 𝓝[≠] cW, pW u ≠ 0 := by
    rcases hpWan.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    · refine absurd (analyticOrderAt_eq_top.2 ?_) hordfin
      filter_upwards [h0] with z hz
      rw [hz, sub_zero]
    · exact h1
  have p2 : ∀ᶠ u in 𝓝[≠] cW, deriv pW u ≠ 0 := by
    rcases hpWan.deriv.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    · exact absurd (h0.filter_mono nhdsWithin_le_nhds)
        (not_eventually_deriv_chartRead_eq_zero hF' W hφπW hφπnc)
    · exact h1
  set S : Set (Place ℂ F') := ⋃ i : Fin n, {w | g i ≠ 0 ∧ w.ord (g i) ≠ 0} with hSdef
  have hSfin : S.Finite := by
    refine Set.finite_iUnion fun i => ?_
    by_cases hgi : g i = 0
    · convert Set.finite_empty
      ext w
      simp [hgi]
    · exact (finite_setOf_ord_ne_zero (K := ℂ) hgi).subset fun w hw => hw.2
  have p3 : ∀ᶠ u in 𝓝[≠] cW, ∀ i, g i ≠ 0 → (σW u).ord (g i) = 0 := by
    filter_upwards [eventually_symm_notMem W S hSfin] with u hu i hgi
    by_contra hne
    exact hu (Set.mem_iUnion.2 ⟨i, hgi, hne⟩)
  have p4 : ∀ᶠ u in 𝓝[≠] cW, ∀ i,
      W.readDifferential (Differential.pullbackAlong ψ (b i)) u =
        W.chartRead (g i) u * deriv pW u := by
    refine Filter.eventually_all.2 fun i => ?_
    have h2 := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
      F' hfg' hF' W hφπW (g i)).1
    rw [← hg i] at h2
    exact h2
  have hpunct : ∀ᶠ u in 𝓝 cW, u ≠ cW → pW u ≠ 0 ∧ deriv pW u ≠ 0 ∧
      (∀ i, g i ≠ 0 → (σW u).ord (g i) = 0) ∧ ∀ i,
      W.readDifferential (Differential.pullbackAlong ψ (b i)) u =
        W.chartRead (g i) u * deriv pW u :=
    eventually_nhdsWithin_iff.1 (p1.and (p2.and (p3.and p4)))

  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.1
    (e1.and (e2.and (e3.and (e9.and hpunct))))
  have hρA : Metric.ball cW ρ ⊆ Metric.ball cW rA := fun u hu => (hall u hu).1
  refine ⟨ρ, Ψ, hρ, fun u hu => htarA (hρA hu),
    fun u hu => ⟨(hall u hu).2.1.1, (hall u hu).2.1.2, (hall u hu).2.2.1.1, (hall u hu).2.2.1.2⟩,
    fun u hu => (hall u hu).2.2.2.1, hpWc, fun i u hu => hΨan i u (hρA hu),
    fun u hu => hΨAJ u (hρA hu), ?_⟩

  intro u hu hne
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (hall u hu).2.2.2.2 hne
  refine ⟨hp1, hp2, hp3, fun i => ?_⟩
  rw [← hp4 i]
  exact hΨd i u (hρA hu)

end LocalData

end AlgebraicCurve.HurwitzLocalProof

open AlgebraicCurve.HurwitzLocalProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (F' : Type*) [Field F'] [Algebra ℂ F'] [HasPrincipalDivisors ℂ F']
    (φ ψ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong ℂ ψ)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ G : Fin n → ℂ → ℂ,
        (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (G i) (P.readDifferential (Differential.correspondence φ ψ (b i)) z) z) ∧
        ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiDiv b P₀ (Divisor.correspondence φ ψ hφ hψ
                (Finsupp.single ((extChartAt 𝓘(ℂ, ℂ) P).symm z) 1)) -
              abelJacobiDiv b P₀ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)) -
              (fun i => G i z - G i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by
  classical
  set Λ := pathPeriodLattice b with hΛ
  set π : F := P.dCoordFn with hπ
  set zP : ℂ := extChartAt 𝓘(ℂ, ℂ) P P with hzP
  set R : ℂ → ℂ := P.chartRead π with hR
  set TΩ : Ω[F⁄ℂ] →ₗ[ℂ] Ω[F⁄ℂ] := Differential.correspondence φ ψ with hTΩ
  set T : Divisor ℂ F →+ Divisor ℂ F := Divisor.correspondence φ ψ hφ hψ with hT
  set A : Place ℂ F → (Fin n → ℂ) := fun v => abelJacobiVec b P₀ v with hAdef

  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hFc : ChartCompatible F := hF
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  have hrat : ∀ v : Place ℂ F, v.IsRational := fun v => isRational v

  obtain ⟨hfg', hcurve'⟩ := roof_hfg_and_isCurveOver (K := ℂ) hfg ψ hfin
  haveI : IsCurveOver ℂ F' := hcurve'
  obtain ⟨tX', cX', hmX', hcX', htX', -, hF'⟩ :=
    AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex F' hfg'
  letI : TopologicalSpace (Place ℂ F') := tX'
  letI : ChartedSpace ℂ (Place ℂ F') := cX'
  haveI : IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F') := hmX'
  haveI : CompactSpace (Place ℂ F') := hcX'
  haveI : T2Space (Place ℂ F') := htX'
  have hF'c : ChartCompatible F' := hF'
  have hrat' : ∀ w : Place ℂ F', w.IsRational := fun w => isRational w
  haveI : Nontrivial Ω[F'⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F')

  have hfinφ : FiniteAlong ℂ φ := by
    obtain ⟨Tg, hTg⟩ := exists_finset_adjoin_eq_top (K := ℂ) (F' := F') hfg'
    exact finiteAlong_of_isIntegral_of_adjoin_eq_top φ hφ Tg hTg
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
  have hsepφ : SeparableAlong ℂ φ := AlgebraicCurve.separableAlong_of_charZero φ hφ

  have hπP : π ∈ P.toValuationSubring := dCoordFn_mem P
  obtain ⟨hRan, hR0, hRd⟩ := chartRead_dCoordFn hFc P
  have hRan' : AnalyticAt ℂ R zP := hRan
  have hR0' : R zP = 0 := hR0
  have hRd' : deriv R zP ≠ 0 := hRd
  have hπnc : ∀ a : ℂ, π - algebraMap ℂ F a ≠ 0 := by
    intro a h
    have h0 := ord_algebraMap P a
    rw [← sub_eq_zero.1 h, P.ord_dCoordFn] at h0
    exact one_ne_zero h0

  have hφπord : ∀ w : Place ℂ F', w.ord (φ π) =
      w.ramificationIndexAlong φ * (w.restrictAlong φ hφ).ord π :=
    fun w => Place.ord_restrictAlong φ hφ w π
  have hepos : ∀ w : Place ℂ F', 0 < w.ramificationIndexAlong φ :=
    fun w => ramificationIndexAlong_pos φ hφ w
  obtain ⟨W₁, hW₁⟩ := AlgebraicCurve.Place.restrictAlong_surjective φ hφ hfinφ hsepφ P
  have hW₁' : W₁.restrictAlong φ hφ = P := hW₁
  have hDφπ : KaehlerDifferential.D ℂ F' (φ π) ≠ 0 := by
    obtain ⟨y, hy, hyfin⟩ := hfg'
    haveI := hyfin
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ ({y} : Set F')) F' :=
      Algebra.IsAlgebraic.of_finite _ _
    refine AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero y W₁ ?_
    rw [hφπord W₁, hW₁', P.ord_dCoordFn, mul_one]
    exact_mod_cast (hepos W₁).ne'

  have hcoef : ∀ i, ∃ gi : F', gi • KaehlerDifferential.D ℂ F' (φ π) =
      Differential.pullbackAlong ψ (b i) := fun i =>
    (finrank_eq_one_iff_of_nonzero' _ hDφπ).1 IsCurveOver.finrank_kaehler _
  choose g hg' using hcoef
  have hg : ∀ i, Differential.pullbackAlong ψ (b i) =
      g i • KaehlerDifferential.D ℂ F' (φ π) := fun i => (hg' i).symm
  set c : Fin n → F := fun i => (letI := algebraAlong φ; Algebra.trace F F' (g i)) with hc
  haveI := hgen P
  have hTΩc : ∀ i, TΩ (b i) = c i • P.dCoord := by
    intro i
    rw [hTΩ, Differential.correspondence_apply, hg i, ← Differential.pullbackAlong_D,
      Differential.traceAlong_smul_pullbackAlong φ hsepφ, hπ, ← P.dCoord_eq_D_dCoordFn]
  have hcoefP : ∀ i, P.differentialCoeff (TΩ (b i)) = c i := fun i =>
    P.differentialCoeff_unique (hTΩc i)
  have hread : ∀ i z, P.readDifferential (TΩ (b i)) z = P.chartRead (c i) z * deriv R z :=
    fun i z => by rw [Place.readDifferential_apply, hcoefP i]
  have hTreg : ∀ i, TΩ (b i) ∈ regularDifferentials ℂ F := fun i =>
    AlgebraicCurve.Differential.correspondence_mem_regularDifferentials ℂ F F' hfg φ ψ hφ hψ hfin
      (hb i)
  have hcmem : ∀ i, c i ∈ P.toValuationSubring := fun i => by
    rw [← hcoefP i]; exact differentialCoeff_mem P (hTreg i)

  set LP := hRan'.hasStrictDerivAt.localInverse R (deriv R zP) zP hRd' with hLP
  have hleftP : ∀ᶠ x in 𝓝 zP, LP (R x) = x := hRan'.hasStrictDerivAt.eventually_left_inverse hRd'
  obtain ⟨r₁, hr₁, hball₁⟩ : ∃ r₁ > 0, ∀ ζ ∈ Metric.ball zP r₁,
      ζ ∈ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
        π ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm ζ).toValuationSubring ∧
        AnalyticAt ℂ R ζ ∧ deriv R ζ ≠ 0 ∧ LP (R ζ) = ζ := by
    refine Metric.eventually_nhds_iff_ball.1 ?_
    have e1 : ∀ᶠ ζ in 𝓝 zP, ζ ∈ (extChartAt 𝓘(ℂ, ℂ) P).target := extChartAt_target_mem_nhds P
    have e2 : ∀ᶠ ζ in 𝓝 zP, π ∈ ((extChartAt 𝓘(ℂ, ℂ) P).symm ζ).toValuationSubring := by
      have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) P).preimage_mem_nhds
        (t := {w' : Place ℂ F | π ∈ w'.toValuationSubring})
        (by rw [extChartAt_to_inv]; exact (isOpen_setOf_mem π).mem_nhds hπP)
      exact this
    have e3 : ∀ᶠ ζ in 𝓝 zP, AnalyticAt ℂ R ζ := hRan'.eventually_analyticAt
    have e4 : ∀ᶠ ζ in 𝓝 zP, deriv R ζ ≠ 0 := hRan'.deriv.continuousAt.eventually_ne hRd'
    exact e1.and (e2.and (e3.and (e4.and hleftP)))
  have hRinj : ∀ ζ ∈ Metric.ball zP r₁, ∀ ζ' ∈ Metric.ball zP r₁, R ζ = R ζ' → ζ = ζ' := by
    intro ζ hζ ζ' hζ' h
    rw [← (hball₁ ζ hζ).2.2.2.2, ← (hball₁ ζ' hζ').2.2.2.2, h]
  have hsrc₁ : ∀ ζ ∈ Metric.ball zP r₁,
      (extChartAt 𝓘(ℂ, ℂ) P).symm ζ ∈ (extChartAt 𝓘(ℂ, ℂ) P).source := fun ζ hζ =>
    (extChartAt 𝓘(ℂ, ℂ) P).map_target (hball₁ ζ hζ).1
  have hRval : ∀ ζ, ((extChartAt 𝓘(ℂ, ℂ) P).symm ζ).evalAt π = R ζ := fun ζ => rfl

  have hordσ : ∀ ζ ∈ Metric.ball zP r₁,
      ((extChartAt 𝓘(ℂ, ℂ) P).symm ζ).ord (π - algebraMap ℂ F (R ζ)) = 1 := by
    intro ζ hζ
    obtain ⟨htar, hπreg, hRanζ, hRdζ, -⟩ := hball₁ ζ hζ
    obtain ⟨htop, hord⟩ := AlgebraicCurve.Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead F hF P _ (hsrc₁ ζ hζ) hπreg (R ζ) (hπnc _)
    rw [(extChartAt 𝓘(ℂ, ℂ) P).right_inv htar] at htop hord
    have h1 : analyticOrderAt (fun z => R z - R ζ) ζ = 1 :=
      hRanζ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hRdζ
    rw [hord]
    simp only [analyticOrderNatAt, hR] at h1 ⊢
    rw [h1]
    rfl

  set Zφ : Finset (Place ℂ F') := Place.fiberAlong φ hφ P with hZφdef
  have hZφ : ∀ W, W ∈ Zφ ↔ W.restrictAlong φ hφ = P := fun W => Place.mem_fiberAlong

  obtain ⟨O, hO, hOdisj⟩ := (Zφ : Set (Place ℂ F')).toFinite.t2_separation
  have hloc : ∀ W : Place ℂ F', ∃ ρ : ℝ, ∃ Ψ : Fin n → ℂ → ℂ, 0 < ρ ∧ (W ∈ Zφ →
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ ⊆ (extChartAt 𝓘(ℂ, ℂ) W).target ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ,
        (extChartAt 𝓘(ℂ, ℂ) W).symm u ∈ O W ∧
          φ π ∈ ((extChartAt 𝓘(ℂ, ℂ) W).symm u).toValuationSubring ∧
          ((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong φ hφ ∈ (extChartAt 𝓘(ℂ, ℂ) P).source ∧
          extChartAt 𝓘(ℂ, ℂ) P (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong φ hφ) ∈
            Metric.ball zP r₁) ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ, AnalyticAt ℂ (W.chartRead (φ π)) u) ∧
      W.chartRead (φ π) (extChartAt 𝓘(ℂ, ℂ) W W) = 0 ∧
      (∀ i, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ, AnalyticAt ℂ (Ψ i) u) ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ,
        A (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong ψ hψ) - A (W.restrictAlong ψ hψ) -
            (fun i => Ψ i u - Ψ i (extChartAt 𝓘(ℂ, ℂ) W W)) ∈ Λ) ∧
      (∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) ρ, u ≠ extChartAt 𝓘(ℂ, ℂ) W W →
        W.chartRead (φ π) u ≠ 0 ∧ deriv (W.chartRead (φ π)) u ≠ 0 ∧
          (∀ i, g i ≠ 0 → ((extChartAt 𝓘(ℂ, ℂ) W).symm u).ord (g i) = 0) ∧
          ∀ i, HasDerivAt (Ψ i) (W.chartRead (g i) u * deriv (W.chartRead (φ π)) u) u)) := by
    intro W
    by_cases hW : W ∈ Zφ
    · obtain ⟨ρ, Ψ, hρ, hrest⟩ := local_data hFc hF'c hfg hfg' hgen φ ψ hφ hψ b hb P₀ P g hg
        r₁ hr₁ W ((hZφ W).1 hW) (O W) (hO W).2 (hO W).1
      exact ⟨ρ, Ψ, hρ, fun _ => hrest⟩
    · exact ⟨1, fun _ _ => 0, one_pos, fun h' => absurd h' hW⟩
  choose ρ Ψ hρ hLD using hloc
  have htar : ∀ W ∈ Zφ, Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W) ⊆
      (extChartAt 𝓘(ℂ, ℂ) W).target := fun W hW => (hLD W hW).1
  have hL1 : ∀ W ∈ Zφ, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W),
      (extChartAt 𝓘(ℂ, ℂ) W).symm u ∈ O W ∧
        φ π ∈ ((extChartAt 𝓘(ℂ, ℂ) W).symm u).toValuationSubring ∧
        ((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong φ hφ ∈ (extChartAt 𝓘(ℂ, ℂ) P).source ∧
        extChartAt 𝓘(ℂ, ℂ) P (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong φ hφ) ∈
          Metric.ball zP r₁ := fun W hW => (hLD W hW).2.1
  have hpan : ∀ W ∈ Zφ, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W),
      AnalyticAt ℂ (W.chartRead (φ π)) u := fun W hW => (hLD W hW).2.2.1
  have hpc : ∀ W ∈ Zφ, W.chartRead (φ π) (extChartAt 𝓘(ℂ, ℂ) W W) = 0 :=
    fun W hW => (hLD W hW).2.2.2.1
  have hΨan : ∀ W ∈ Zφ, ∀ i, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W),
      AnalyticAt ℂ (Ψ W i) u := fun W hW => (hLD W hW).2.2.2.2.1
  have hAJloc : ∀ W ∈ Zφ, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W),
      A (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong ψ hψ) - A (W.restrictAlong ψ hψ) -
        (fun i => Ψ W i u - Ψ W i (extChartAt 𝓘(ℂ, ℂ) W W)) ∈ Λ :=
    fun W hW => (hLD W hW).2.2.2.2.2.1
  have hpunct : ∀ W ∈ Zφ, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W),
      u ≠ extChartAt 𝓘(ℂ, ℂ) W W →
        W.chartRead (φ π) u ≠ 0 ∧ deriv (W.chartRead (φ π)) u ≠ 0 ∧
          (∀ i, g i ≠ 0 → ((extChartAt 𝓘(ℂ, ℂ) W).symm u).ord (g i) = 0) ∧
          ∀ i, HasDerivAt (Ψ W i) (W.chartRead (g i) u * deriv (W.chartRead (φ π)) u) u :=
    fun W hW => (hLD W hW).2.2.2.2.2.2

  set r : Place ℂ F' → ℝ := fun W => ρ W / 2 with hrdef
  have hr : ∀ W, 0 < r W := fun W => by simp only [hrdef]; linarith [hρ W]
  have hrρ : ∀ W, r W < ρ W := fun W => by simp only [hrdef]; linarith [hρ W]
  have hcb : ∀ W, Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) W W) (r W) ⊆
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W) := fun W =>
    Metric.closedBall_subset_ball (hrρ W)
  have hbb' : ∀ W, Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (r W) ⊆
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W) := fun W =>
    Metric.ball_subset_ball (hrρ W).le
  have hsph : ∀ W, Metric.sphere (extChartAt 𝓘(ℂ, ℂ) W W) (r W) ⊆
      Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (ρ W) := fun W =>
    Metric.sphere_subset_closedBall.trans (hcb W)
  have hsph_ne : ∀ W, ∀ u ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) W W) (r W),
      u ≠ extChartAt 𝓘(ℂ, ℂ) W W := fun W u hu => Metric.ne_of_mem_sphere hu (hr W).ne'
  set Dv : Place ℂ F' → Set (Place ℂ F') := fun w =>
    (extChartAt 𝓘(ℂ, ℂ) w).source ∩
      extChartAt 𝓘(ℂ, ℂ) w ⁻¹' Metric.ball (extChartAt 𝓘(ℂ, ℂ) w w) (r w) with hDvdef
  have hDo : ∀ w, IsOpen (Dv w) := fun w =>
    isOpen_extChartAt_preimage' (I := 𝓘(ℂ, ℂ)) w Metric.isOpen_ball
  have hDw : ∀ w, w ∈ Dv w := fun w =>
    ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) w, Metric.mem_ball_self (hr w)⟩

  have hcontφ : Continuous fun w : Place ℂ F' => w.restrictAlong φ hφ :=
    AlgebraicCurve.Place.continuous_restrictAlong F F' hF hF' φ hφ
  set Uo : Set (Place ℂ F') := ⋃ W ∈ Zφ, Dv W with hUodef
  set Vo : Set (Place ℂ F) := ((fun w : Place ℂ F' => w.restrictAlong φ hφ) '' Uoᶜ)ᶜ with hVodef
  have hVo : IsOpen Vo := by
    have hK : IsCompact Uoᶜ := (isOpen_biUnion fun W _ => hDo W).isClosed_compl.isCompact
    exact (hK.image hcontφ).isClosed.isOpen_compl
  have hPVo : P ∈ Vo := by
    rintro ⟨w, hw, hwP⟩
    exact hw (Set.mem_biUnion (Finset.mem_coe.2 ((hZφ w).2 hwP)) (hDw w))
  have hzeros : ∀ w' : Place ℂ F', w'.restrictAlong φ hφ ∈ Vo → ∃ W ∈ Zφ, w' ∈ Dv W := by
    intro w' hw'
    by_contra hcon
    have hU : w' ∈ Uoᶜ := by
      intro hU
      obtain ⟨W, hW, hWD⟩ := Set.mem_iUnion₂.1 hU
      exact hcon ⟨W, Finset.mem_coe.1 hW, hWD⟩
    exact hw' ⟨w', hU, rfl⟩
  have hcirc : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ W ∈ Zφ,
      ∀ u ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) W W) (r W), W.chartRead (φ π) u ≠ t := by
    refine (Filter.eventually_all_finset Zφ).2 fun W hW => ?_
    refine eventually_forall_sphere_ne (fun u hu => (hpan W hW u (hsph W hu)).continuousAt
      |>.continuousWithinAt) fun u hu => (hpunct W hW u (hsph W hu) (hsph_ne W u hu)).1
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 hcirc
  have hcirc' : ∀ t ∈ Metric.ball (0 : ℂ) ε, ∀ W ∈ Zφ,
      ∀ u ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) W W) (r W), W.chartRead (φ π) u ≠ t :=
    fun t ht => hεball ht

  obtain ⟨r₀, hr₀, hr₀ball⟩ : ∃ r₀ > 0, ∀ ζ ∈ Metric.ball zP r₀,
      ζ ∈ Metric.ball zP r₁ ∧ R ζ ∈ Metric.ball (0 : ℂ) ε ∧
        (extChartAt 𝓘(ℂ, ℂ) P).symm ζ ∈ Vo := by
    refine Metric.eventually_nhds_iff_ball.1 ?_
    have e1 : ∀ᶠ ζ in 𝓝 zP, ζ ∈ Metric.ball zP r₁ := Metric.ball_mem_nhds zP hr₁
    have e2 : ∀ᶠ ζ in 𝓝 zP, R ζ ∈ Metric.ball (0 : ℂ) ε := by
      have := hRan'.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (R zP) hε)
      rw [hR0'] at this
      exact this
    have e3 : ∀ᶠ ζ in 𝓝 zP, (extChartAt 𝓘(ℂ, ℂ) P).symm ζ ∈ Vo := by
      refine (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) P).preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact hVo.mem_nhds hPVo
    exact e1.and (e2.and e3)
  have hr₀₁ : ∀ ζ ∈ Metric.ball zP r₀, ζ ∈ Metric.ball zP r₁ := fun ζ hζ => (hr₀ball ζ hζ).1
  have hRε : ∀ ζ ∈ Metric.ball zP r₀, R ζ ∈ Metric.ball (0 : ℂ) ε := fun ζ hζ =>
    (hr₀ball ζ hζ).2.1

  have hH1 : ∀ (W : Place ℂ F') (t : ℂ), ∃ Zf : Finset ℂ, W ∈ Zφ → t ∈ Metric.ball (0 : ℂ) ε →
      (∀ a, a ∈ Zf ↔ a ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (r W) ∧ W.chartRead (φ π) a = t) ∧
      (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          (fun _ => (1 : ℂ)) u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf, (analyticOrderNatAt (fun u => W.chartRead (φ π) u - t) a : ℂ) * 1 ∧
      ∀ i, (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          Ψ W i u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf, (analyticOrderNatAt (fun u => W.chartRead (φ π) u - t) a : ℂ) * Ψ W i a := by
    intro W t
    by_cases hW : W ∈ Zφ
    · by_cases ht : t ∈ Metric.ball (0 : ℂ) ε
      · have hRcl : ∀ u ∈ Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) W W) (r W),
            AnalyticAt ℂ (W.chartRead (φ π)) u := fun u hu => hpan W hW u (hcb W hu)
        obtain ⟨Zf, hZf, hint⟩ :=
          Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (G := fun _ => (1 : ℂ))
            (hr W) hRcl (fun u _ => analyticAt_const) (hcirc' t ht W hW)
        refine ⟨Zf, fun _ _ => ⟨hZf, hint, fun i => ?_⟩⟩
        obtain ⟨Zf', hZf', hint'⟩ :=
          Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (G := Ψ W i)
            (hr W) hRcl (fun u hu => hΨan W hW i u (hcb W hu)) (hcirc' t ht W hW)
        have hZZ : Zf' = Zf := Finset.ext fun a => (hZf' a).trans (hZf a).symm
        rw [hint', hZZ]
      · exact ⟨∅, fun _ h' => absurd h' ht⟩
    · exact ⟨∅, fun h' => absurd h' hW⟩
  choose Zf hZfP using hH1
  have hZf : ∀ W ∈ Zφ, ∀ t ∈ Metric.ball (0 : ℂ) ε, ∀ a,
      a ∈ Zf W t ↔ a ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (r W) ∧ W.chartRead (φ π) a = t :=
    fun W hW t ht => (hZfP W t hW ht).1
  have hI0 : ∀ W ∈ Zφ, ∀ t ∈ Metric.ball (0 : ℂ) ε,
      (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          (fun _ => (1 : ℂ)) u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf W t, (analyticOrderNatAt (fun u => W.chartRead (φ π) u - t) a : ℂ) * 1 :=
    fun W hW t ht => (hZfP W t hW ht).2.1
  have hIΨ : ∀ W ∈ Zφ, ∀ t ∈ Metric.ball (0 : ℂ) ε, ∀ i,
      (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          Ψ W i u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf W t, (analyticOrderNatAt (fun u => W.chartRead (φ π) u - t) a : ℂ) *
            Ψ W i a :=
    fun W hW t ht => (hZfP W t hW ht).2.2

  set m : Place ℂ F' → ℂ → ℂ → ℕ := fun W t a =>
    analyticOrderNatAt (fun u => W.chartRead (φ π) u - t) a with hmdef
  set sy : Place ℂ F' → ℂ → Place ℂ F' := fun W a => (extChartAt 𝓘(ℂ, ℂ) W).symm a with hsydef
  set Ψc : Place ℂ F' → (Fin n → ℂ) := fun W i => Ψ W i (extChartAt 𝓘(ℂ, ℂ) W W) with hΨcdef
  set RWp : Place ℂ F' → Place ℂ F := fun W => W.restrictAlong ψ hψ with hRWp
  set Q : ℂ → Place ℂ F := fun ζ => (extChartAt 𝓘(ℂ, ℂ) P).symm ζ with hQdef

  have hφval : ∀ (w : Place ℂ F') (f : F), w.evalAt (φ f) = (w.restrictAlong φ hφ).evalAt f :=
    fun w f => (evalAt_restrictAlong φ hφ w (hrat' w) (hrat _) f).symm
  have hφsub : ∀ t : ℂ, φ (π - algebraMap ℂ F t) = φ π - algebraMap ℂ F' t := fun t => by
    rw [map_sub, AlgHom.commutes]

  have hordw : ∀ ζ ∈ Metric.ball zP r₀, ∀ w' : Place ℂ F', w'.restrictAlong φ hφ = Q ζ →
      w'.ord (φ π - algebraMap ℂ F' (R ζ)) = w'.ramificationIndexAlong φ := by
    intro ζ hζ w' hw'
    rw [← hφsub, Place.ord_restrictAlong φ hφ w', hw', hQdef]
    simp only
    rw [hordσ ζ (hr₀₁ ζ hζ), mul_one]

  have hfibA : ∀ ζ ∈ Metric.ball zP r₀, ∀ w' ∈ Place.fiberAlong φ hφ (Q ζ),
      ∃ W ∈ Zφ, w' ∈ (extChartAt 𝓘(ℂ, ℂ) W).source ∧
        extChartAt 𝓘(ℂ, ℂ) W w' ∈ Zf W (R ζ) ∧
        (w'.ramificationIndexAlong φ : ℤ) = m W (R ζ) (extChartAt 𝓘(ℂ, ℂ) W w') := by
    intro ζ hζ w' hw'
    have hw'Q : w'.restrictAlong φ hφ = Q ζ := Place.mem_fiberAlong.1 hw'
    have hordpos : 0 < w'.ord (φ π - algebraMap ℂ F' (R ζ)) := by
      rw [hordw ζ hζ w' hw'Q]; exact_mod_cast hepos w'
    obtain ⟨w'', hW, hD⟩ := hzeros w' (by rw [hw'Q]; exact (hr₀ball ζ hζ).2.2)
    obtain ⟨hsrc, hball⟩ := hD
    have hball' : extChartAt 𝓘(ℂ, ℂ) w'' w' ∈
        Metric.ball (extChartAt 𝓘(ℂ, ℂ) w'' w'') (r w'') := hball
    have hfw : φ π ∈ w'.toValuationSubring := by
      have := (hL1 w'' hW _ (hbb' w'' hball')).2.1
      rwa [(extChartAt 𝓘(ℂ, ℂ) w'').left_inv hsrc] at this
    have hRa : w''.chartRead (φ π) (extChartAt 𝓘(ℂ, ℂ) w'' w') = R ζ := by
      rw [Place.chartRead_apply, (extChartAt 𝓘(ℂ, ℂ) w'').left_inv hsrc, hφval, hw'Q]
      exact hRval ζ
    obtain ⟨-, hord⟩ := AlgebraicCurve.Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead F' hF' w'' w' hsrc hfw (R ζ) (by
      intro h0; rw [h0, Place.ord_zero] at hordpos; exact lt_irrefl _ hordpos)
    refine ⟨w'', hW, hsrc, (hZf w'' hW _ (hRε ζ hζ) _).2 ⟨hball', hRa⟩, ?_⟩
    rw [← hordw ζ hζ w' hw'Q, hord]

  have hfibB : ∀ ζ ∈ Metric.ball zP r₀, ∀ W ∈ Zφ, ∀ a ∈ Zf W (R ζ),
      sy W a ∈ (extChartAt 𝓘(ℂ, ℂ) W).source ∧ extChartAt 𝓘(ℂ, ℂ) W (sy W a) = a ∧
      a ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) (r W) ∧ W.chartRead (φ π) a = R ζ ∧
      sy W a ∈ Place.fiberAlong φ hφ (Q ζ) ∧ 0 < m W (R ζ) a ∧
      ((sy W a).ramificationIndexAlong φ : ℤ) = m W (R ζ) a := by
    intro ζ hζ W hW a ha
    obtain ⟨haball, hRa⟩ := (hZf W hW _ (hRε ζ hζ) a).1 ha
    have hatar : a ∈ (extChartAt 𝓘(ℂ, ℂ) W).target := htar W hW (hbb' W haball)
    have hsrc : sy W a ∈ (extChartAt 𝓘(ℂ, ℂ) W).source := (extChartAt 𝓘(ℂ, ℂ) W).map_target hatar
    have hφa : extChartAt 𝓘(ℂ, ℂ) W (sy W a) = a := (extChartAt 𝓘(ℂ, ℂ) W).right_inv hatar
    obtain ⟨-, hfw, hQ'src, hQ'ball⟩ := hL1 W hW a (hbb' W haball)

    set ζ' := extChartAt 𝓘(ℂ, ℂ) P ((sy W a).restrictAlong φ hφ) with hζ'
    have hQ' : (sy W a).restrictAlong φ hφ = Q ζ' := by
      rw [hQdef]; exact ((extChartAt 𝓘(ℂ, ℂ) P).left_inv hQ'src).symm
    have hRζ' : R ζ' = R ζ := by
      calc R ζ' = (Q ζ').evalAt π := (hRval ζ').symm
        _ = ((sy W a).restrictAlong φ hφ).evalAt π := by rw [hQ']
        _ = (sy W a).evalAt (φ π) := (hφval _ _).symm
        _ = W.chartRead (φ π) a := rfl
        _ = R ζ := hRa
    have hζζ : ζ' = ζ := hRinj ζ' hQ'ball ζ (hr₀₁ ζ hζ) hRζ'
    have hfib : sy W a ∈ Place.fiberAlong φ hφ (Q ζ) := by
      rw [Place.mem_fiberAlong, hQ', hζζ]
    obtain ⟨htop, hord⟩ := AlgebraicCurve.Place.ord_sub_algebraMap_eq_analyticOrderNatAt_chartRead F' hF' W (sy W a) hsrc hfw (R ζ) (by
      intro h0
      have := hordw ζ hζ (sy W a) (by rw [hQ', hζζ])
      rw [h0, Place.ord_zero] at this
      exact absurd this.symm (by exact_mod_cast (hepos (sy W a)).ne'))
    rw [hφa] at htop hord
    have hem : ((sy W a).ramificationIndexAlong φ : ℤ) = m W (R ζ) a := by
      rw [← hordw ζ hζ (sy W a) (by rw [hQ', hζζ]), hord]
    refine ⟨hsrc, hφa, haball, hRa, hfib, ?_, hem⟩
    have := hepos (sy W a)
    omega

  have hsurj : ∀ ζ ∈ Metric.ball zP r₀, ∀ w ∈ Place.fiberAlong φ hφ (Q ζ),
      ∃ W ∈ Zφ, ∃ a ∈ Zf W (R ζ), sy W a = w := by
    intro ζ hζ w hw
    obtain ⟨W, hW, hwsrc, ha, -⟩ := hfibA ζ hζ w hw
    exact ⟨W, hW, _, ha, (extChartAt 𝓘(ℂ, ℂ) W).left_inv hwsrc⟩
  have hmem : ∀ ζ ∈ Metric.ball zP r₀, ∀ W ∈ Zφ, ∀ a ∈ Zf W (R ζ),
      sy W a ∈ Place.fiberAlong φ hφ (Q ζ) :=
    fun ζ hζ W hW a ha => (hfibB ζ hζ W hW a ha).2.2.2.2.1
  have hinj : ∀ ζ ∈ Metric.ball zP r₀, ∀ W ∈ Zφ, ∀ W' ∈ Zφ, ∀ a ∈ Zf W (R ζ),
      ∀ a' ∈ Zf W' (R ζ), sy W a = sy W' a' → W = W' ∧ a = a' := by
    intro ζ hζ W hW W' hW' a ha a' ha' heq
    obtain ⟨-, hφa, haball, -⟩ := hfibB ζ hζ W hW a ha
    obtain ⟨-, hφa', haball', -⟩ := hfibB ζ hζ W' hW' a' ha'
    have hO1 : sy W a ∈ O W := (hL1 W hW a (hbb' W haball)).1
    have hO2 : sy W' a' ∈ O W' := (hL1 W' hW' a' (hbb' W' haball')).1
    have hWW : W = W' := by
      by_contra hne'
      have hdisj := hOdisj (Finset.mem_coe.2 hW) (Finset.mem_coe.2 hW') hne'
      rw [← heq] at hO2
      exact Set.disjoint_left.1 hdisj hO1 hO2
    subst hWW
    exact ⟨rfl, by rw [← hφa, ← hφa', heq]⟩

  have hAJT : ∀ ζ ∈ Metric.ball zP r₀,
      abelJacobiDiv b P₀ (T (Finsupp.single (Q ζ) 1)) =
        ∑ W ∈ Zφ, ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) • A (RWp (sy W a)) := by
    intro ζ hζ
    rw [hT, correspondence_single φ ψ hφ hψ (Q ζ), map_sum]
    simp only [abelJacobiDiv_single]
    rw [sum_eq_sum_sum (Place.fiberAlong φ hφ (Q ζ)) Zφ (fun W => Zf W (R ζ)) sy (hsurj ζ hζ)
      (hmem ζ hζ) (hinj ζ hζ)]
    refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun a ha => ?_
    rw [(hfibB ζ hζ W hW a ha).2.2.2.2.2.2, natCast_zsmul, Nat.cast_smul_eq_nsmul]

  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set k : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹ with hkdef
  set Gt : ℂ → (Fin n → ℂ) := fun ζ => ∑ W ∈ Zφ,
      ((k * ∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          (fun _ => (1 : ℂ)) u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - R ζ)) •
          (A (RWp W) - Ψc W) +
        k • fun i => ∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          Ψ W i u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - R ζ)) with hGtdef
  set Gt' : ℂ → (Fin n → ℂ) := fun ζ => ∑ W ∈ Zφ,
      ((k * ((∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          deriv (fun _ => (1 : ℂ)) u / (W.chartRead (φ π) u - R ζ)) * deriv R ζ)) •
          (A (RWp W) - Ψc W) +
        k • fun i => (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          deriv (Ψ W i) u / (W.chartRead (φ π) u - R ζ)) * deriv R ζ) with hGt'def

  have hAJL : ∀ ζ ∈ Metric.ball zP r₀, abelJacobiDiv b P₀ (T (Finsupp.single (Q ζ) 1)) - Gt ζ ∈ Λ := by
    intro ζ hζ
    have ht := hRε ζ hζ
    have hL : Gt ζ = ∑ W ∈ Zφ, ((∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ)) • (A (RWp W) - Ψc W) +
        fun i => ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) * Ψ W i a) := by
      simp only [hGtdef]
      refine Finset.sum_congr rfl fun W hW => ?_
      rw [hI0 W hW _ ht]
      congr 1
      · congr 1
        rw [← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
        simp only [mul_one]
        rfl
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hIΨ W hW _ ht i, ← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
    rw [hAJT ζ hζ, hL, ← Finset.sum_sub_distrib]
    refine Λ.sum_mem fun W hW => ?_
    have hterm : ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) • A (RWp (sy W a)) -
        ((∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ)) • (A (RWp W) - Ψc W) +
          fun i => ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) * Ψ W i a) =
        ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) •
          (A (RWp (sy W a)) - A (RWp W) - ((fun i => Ψ W i a) - Ψc W)) := by
      have hfun : (fun i => ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) * Ψ W i a) =
          ∑ a ∈ Zf W (R ζ), (m W (R ζ) a : ℂ) • (fun i => Ψ W i a) := by
        funext i
        simp [Finset.sum_apply, smul_eq_mul]
      rw [hfun, Finset.sum_smul]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [hterm]
    refine Λ.sum_mem fun a ha => ?_
    obtain ⟨-, -, haball, -⟩ := hfibB ζ hζ W hW a ha
    rw [Nat.cast_smul_eq_nsmul ℂ, ← natCast_zsmul]
    exact Λ.smul_mem _ (hAJloc W hW a (hbb' W haball))

  have hLder : ∀ ζ ∈ Metric.ball zP r₀, HasDerivAt Gt (Gt' ζ) ζ := by
    intro ζ hζ
    have ht := hRε ζ hζ
    have hRζ : HasDerivAt R (deriv R ζ) ζ := (hball₁ ζ (hr₀₁ ζ hζ)).2.2.1.differentiableAt.hasDerivAt
    simp only [hGtdef, hGt'def]
    refine HasDerivAt.fun_sum fun W hW => ?_
    have hsphR : ∀ u ∈ Metric.sphere (extChartAt 𝓘(ℂ, ℂ) W W) (r W),
        AnalyticAt ℂ (W.chartRead (φ π)) u := fun u hu => hpan W hW u (hsph W hu)
    have hB0 := Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub (G := fun _ => (1 : ℂ))
      (hr W) hsphR (fun u _ => analyticAt_const) (hcirc' _ ht W hW)
    have hB0' := hB0.comp ζ hRζ
    have hBi : ∀ i, HasDerivAt (fun s => ∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          Ψ W i u * deriv (W.chartRead (φ π)) u / (W.chartRead (φ π) u - R s))
        ((∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
          deriv (Ψ W i) u / (W.chartRead (φ π) u - R ζ)) * deriv R ζ) ζ := fun i =>
      (Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub (hr W) hsphR
        (fun u hu => hΨan W hW i u (hsph W hu)) (hcirc' _ ht W hW)).comp ζ hRζ
    exact ((hB0'.const_mul k).smul_const _).add
      (HasDerivAt.const_smul k (hasDerivAt_pi.2 fun i => hBi i))

  have hLder_eq : ∀ ζ ∈ Metric.ball zP r₀, ζ ≠ zP → ∀ i,
      Gt' ζ i = P.readDifferential (TΩ (b i)) ζ := by
    intro ζ hζ hζne i
    have ht := hRε ζ hζ
    have hRζ0 : R ζ ≠ 0 := by
      intro h0
      exact hζne (hRinj ζ (hr₀₁ ζ hζ) zP (Metric.mem_ball_self hr₁) (by rw [h0, hR0']))
    have hJ0 : ∀ W : Place ℂ F', (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
        deriv (fun _ : ℂ => (1 : ℂ)) u / (W.chartRead (φ π) u - R ζ)) = 0 := fun W => by
      simp [circleIntegral]

    have hsimpleZ : ∀ W ∈ Zφ, ∀ a ∈ Zf W (R ζ), a ≠ extChartAt 𝓘(ℂ, ℂ) W W ∧
        deriv (W.chartRead (φ π)) a ≠ 0 ∧
        (∀ j, g j ≠ 0 → (sy W a).ord (g j) = 0) ∧
        ∀ j, HasDerivAt (Ψ W j) (W.chartRead (g j) a * deriv (W.chartRead (φ π)) a) a := by
      intro W hW a ha
      obtain ⟨-, -, haball, hRa, -⟩ := hfibB ζ hζ W hW a ha
      have hac : a ≠ extChartAt 𝓘(ℂ, ℂ) W W := fun h0 =>
        hRζ0 (by rw [← hRa, h0, hpc W hW])
      exact ⟨hac, (hpunct W hW a (hbb' W haball) hac).2⟩
    have hm1 : ∀ W ∈ Zφ, ∀ a ∈ Zf W (R ζ), m W (R ζ) a = 1 := by
      intro W hW a ha
      obtain ⟨-, -, haball, hRa, -⟩ := hfibB ζ hζ W hW a ha
      obtain ⟨-, hda, -⟩ := hsimpleZ W hW a ha
      have h1 : analyticOrderAt (fun u => W.chartRead (φ π) u - R ζ) a = 1 := by
        have := (hpan W hW a (hbb' W haball)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hda
        rwa [hRa] at this
      simp only [hmdef, analyticOrderNatAt, h1, ENat.toNat_one]
    have hJ : ∀ W ∈ Zφ, (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
        deriv (Ψ W i) u / (W.chartRead (φ π) u - R ζ)) =
        2 * Real.pi * Complex.I * ∑ a ∈ Zf W (R ζ), (sy W a).evalAt (g i) := by
      intro W hW
      have hΨ'an : ∀ u ∈ Metric.closedBall (extChartAt 𝓘(ℂ, ℂ) W W) (r W),
          AnalyticAt ℂ (deriv (Ψ W i)) u := fun u hu => (hΨan W hW i u (hcb W hu)).deriv
      rw [Complex.circleIntegral_div_sub_eq_sum_div_deriv (hr W) (fun u hu => hpan W hW u (hcb W hu))
        hΨ'an (hcirc' _ ht W hW) (Zf W (R ζ)) (hZf W hW _ ht)
        (fun a ha => (hsimpleZ W hW a ha).2.1)]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨-, hda, -, hder⟩ := hsimpleZ W hW a ha
      rw [(hder i).deriv, mul_div_cancel_right₀ _ hda, Place.chartRead_apply]

    have htrace : ∑ w ∈ Place.fiberAlong φ hφ (Q ζ), w.evalAt (g i) = (Q ζ).evalAt (c i) := by
      by_cases hgi : g i = 0
      · have hci : c i = 0 := by simp only [hc, hgi, map_zero]
        rw [hci, hgi]
        simp only [evalAt_zero, Finset.sum_const_zero]
      · letI := algebraAlong φ
        haveI := isScalarTower_along φ
        haveI : FiniteDimensional F F' := hfinφ
        haveI : Algebra.IsSeparable F F' := hsepφ
        have hordfib : ∀ w ∈ (Q ζ).fiber F', w.ord (g i) = 0 := by
          intro w hw
          obtain ⟨W, hW, a, ha, rfl⟩ := hsurj ζ hζ w hw
          exact (hsimpleZ W hW a ha).2.2.1 i hgi
        have hone : ∀ w ∈ (Q ζ).fiber F', w.ramificationIndex F = 1 := by
          intro w hw
          obtain ⟨W, hW, a, ha, rfl⟩ := hsurj ζ hζ w hw
          have h1 := (hfibB ζ hζ W hW a ha).2.2.2.2.2.2
          rw [hm1 W hW a ha, Nat.cast_one] at h1
          exact_mod_cast h1
        have key := AlgebraicCurve.Place.evalAt_trace_eq_sum_fiber (K := ℂ) (Q ζ) (hrat _)
          (fun w _ => hrat' w) (g i) hgi hordfib
        rw [key]
        symm
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [hone w hw, one_smul]

    have hv_eq : ∀ W ∈ Zφ,
        ((k * ((∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
            deriv (fun _ => (1 : ℂ)) u / (W.chartRead (φ π) u - R ζ)) * deriv R ζ)) •
            (A (RWp W) - Ψc W) +
          k • fun i => (∮ u in C(extChartAt 𝓘(ℂ, ℂ) W W, r W),
            deriv (Ψ W i) u / (W.chartRead (φ π) u - R ζ)) * deriv R ζ) i =
        deriv R ζ * ∑ a ∈ Zf W (R ζ), (sy W a).evalAt (g i) := by
      intro W hW
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ0 W, hJ W hW, mul_zero, zero_mul,
        zero_add]
      rw [← mul_assoc, ← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul, mul_comm]
    simp only [hGt'def]
    rw [Finset.sum_apply, Finset.sum_congr rfl hv_eq, ← Finset.mul_sum,
      ← sum_eq_sum_sum (Place.fiberAlong φ hφ (Q ζ)) Zφ (fun W => Zf W (R ζ)) sy (hsurj ζ hζ)
        (hmem ζ hζ) (hinj ζ hζ) (fun w => w.evalAt (g i)),
      htrace, hread i ζ, mul_comm]
    rfl

  have hGder : ∀ i, ∀ ζ ∈ Metric.ball zP r₀,
      HasDerivAt (fun ζ => Gt ζ i) (P.readDifferential (TΩ (b i)) ζ) ζ := by
    intro i ζ hζ
    have hcomp : ∀ ζ ∈ Metric.ball zP r₀, HasDerivAt (fun ζ => Gt ζ i) (Gt' ζ i) ζ :=
      fun ζ hζ => (hasDerivAt_pi.1 (hLder ζ hζ)) i
    have heq : Gt' ζ i = P.readDifferential (TΩ (b i)) ζ := by
      by_cases hζne : ζ = zP
      · subst hζne

        have hdiff : DifferentiableOn ℂ (fun ζ => Gt ζ i) (Metric.ball zP r₀) := fun s hs =>
          (hcomp s hs).differentiableAt.differentiableWithinAt
        have hA : AnalyticAt ℂ (fun ζ => Gt ζ i) zP :=
          hdiff.analyticAt (Metric.ball_mem_nhds zP hr₀)
        have hc1 : ContinuousAt (fun ζ => Gt' ζ i) zP := by
          refine hA.deriv.continuousAt.congr ?_
          filter_upwards [Metric.ball_mem_nhds zP hr₀] with s hs
          exact (hcomp s hs).deriv
        have hc2 : ContinuousAt (fun ζ => P.readDifferential (TΩ (b i)) ζ) zP := by
          have h1 : ContinuousAt (P.chartRead (c i)) zP :=
            (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF P
              (hcmem i)).continuousAt
          have h2 : ContinuousAt (deriv R) zP := hRan'.deriv.continuousAt
          exact (h1.mul h2).congr (Filter.Eventually.of_forall fun s => (hread i s).symm)
        refine eq_of_eventually_eq_of_continuousAt hc1 hc2 ?_
        have hb : ∀ᶠ s in 𝓝 zP, s ∈ Metric.ball zP r₀ := Metric.ball_mem_nhds zP hr₀
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds hb, self_mem_nhdsWithin]
          with s hs hs'
        exact hLder_eq s hs hs' i
      · exact hLder_eq ζ hζ hζne i
    rw [← heq]
    exact hcomp ζ hζ

  refine ⟨r₀, hr₀, fun ζ hζ => (hball₁ ζ (hr₀₁ ζ hζ)).1, fun i ζ => Gt ζ i,
    fun i ζ hζ => hGder i ζ hζ, fun ζ hζ => ?_⟩
  have h1 := hAJL ζ hζ
  have h0 := hAJL zP (Metric.mem_ball_self hr₀)
  have hQ0 : Q zP = P := by rw [hQdef, hzP]; exact extChartAt_to_inv P
  rw [hQ0] at h0
  have hEq : abelJacobiDiv b P₀ (T (Finsupp.single (Q ζ) 1)) -
      abelJacobiDiv b P₀ (T (Finsupp.single P 1)) - (fun i => Gt ζ i - Gt zP i) =
      (abelJacobiDiv b P₀ (T (Finsupp.single (Q ζ) 1)) - Gt ζ) -
        (abelJacobiDiv b P₀ (T (Finsupp.single P 1)) - Gt zP) := by
    have : (fun i => Gt ζ i - Gt zP i) = Gt ζ - Gt zP := rfl
    rw [this]; abel
  rw [hEq]
  exact Λ.sub_mem h1 h0

end

end S_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice (solution)
