-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0618baf8-5b8b-503b-b6d9-a8f159f6faa7

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_finite_and_ncard_eq_finsum_finrank_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel"
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.evalAt_one IsCurveOver Place.evalAt_mul_of_mem Place.evalAt_algebraMap_eq NodeAnnulusEngine.finite_and_ncard_eq_finsum_finrank_of_forall_iff_evalAt_eq_zero NodeAnnulusEngine.toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero"
namespace NodeAnnulusEngine
p2m_export "AlgebraicCurve.NodeAnnulusEngine" "finite_and_ncard_eq_finsum_finrank_of_forall_iff_evalAt_eq_zero toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero"
namespace DictAssembly
p2m_open "AlgebraicCurve.NodeAnnulusEngine AlgebraicCurve"

section PlaceHelpers

theorem vsub_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f⁻¹ ∈ O :=
  O.mem_of_valuation_le_one _ (by
    rw [map_inv₀, show O.valuation f = 1 from (O.valuation_eq_one_iff ⟨f, hf⟩).mp hu, inv_one])

theorem vsub_isUnit_of_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hf0 : f ≠ 0) (hi : f⁻¹ ∈ O) : IsUnit (⟨f, hf⟩ : O) :=
  isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

theorem vsub_ne_zero_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f ≠ 0 := by
  rintro rfl
  have h0 : (⟨0, hf⟩ : O) = 0 := Subtype.ext rfl
  rw [h0] at hu
  exact not_isUnit_zero hu

theorem vsub_not_isUnit_algebraMap {L F : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (O : ValuationSubring F) (hO : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A) (a : ↥A)
    (ha : a ∈ maximalIdeal ↥A) : ¬ IsUnit (⟨algebraMap L F (a : L), (hO a).mpr a.2⟩ : O) := by
  intro hu
  have hi := vsub_inv_mem O _ hu
  rw [← map_inv₀, hO] at hi
  apply (IsLocalRing.mem_maximalIdeal _).mp ha
  rcases eq_or_ne a 0 with rfl | ha0
  · exfalso
    have : (⟨algebraMap L F ((0 : ↥A) : L), (hO _).mpr (0 : ↥A).2⟩ : O) = 0 := Subtype.ext (by simp)
    rw [this] at hu
    exact not_isUnit_zero hu
  have ha0' : (a : L) ≠ 0 := fun h => ha0 (Subtype.ext h)
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : L)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0')⟩

theorem isUnit_transfer {L : Type*} [Field L] (A : ValuationSubring L) {a b : L} (hab : a = b) (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : ↥A)) : ∃ h : b ∈ A, IsUnit (⟨b, h⟩ : ↥A) := by
  subst hab
  exact ⟨ha, hu⟩

theorem vsub_zpow_mem_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) (n : ℤ) : f ^ n ∈ O := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hf m
  · rw [zpow_negSucc]
    refine vsub_inv_mem _ (pow_mem hf _) ?_
    have : (⟨f ^ (m + 1), pow_mem hf (m + 1)⟩ : O) = ⟨f, hf⟩ ^ (m + 1) := Subtype.ext (by simp)
    rw [this]
    exact hu.pow _

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have hle : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have h1 := (WithZero.log_le_log hne one_ne_zero).mpr hle
  rw [WithZero.log_one] at h1
  simp only [Place.ord]
  omega

theorem isUnit_iff_ord_eq_zero {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
  simp only [Place.ord]
  constructor
  · intro h
    rw [h, WithZero.log_one, neg_zero]
  · intro h
    have hne := v.adicValuation_ne_zero hf0
    have hlog : WithZero.log (v.adicValuation f) = 0 := by omega
    rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]

theorem one_le_ord_of_not_isUnit {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : 1 ≤ v.ord f := by
  have h0 := ord_nonneg_of_mem v hf
  have h1 : v.ord f ≠ 0 := fun h => hu ((isUnit_iff_ord_eq_zero v hf hf0).mpr h)
  omega

theorem evalAt_eq_zero_iff_not_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = 0 ↔ ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [← residue_ne_zero_iff_isUnit, not_not, ← v.algebraMap_evalAt hv hf,
    map_eq_zero_iff _ (algebraMap K v.ResidueField).injective]

theorem evalAt_zero' : v.evalAt (0 : F) = 0 := by
  have h := v.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

theorem evalAt_eq_zero_of_ord_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.ord f ≠ 0) : v.evalAt f = 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact evalAt_zero' v
  exact (evalAt_eq_zero_iff_not_isUnit v hv hf).mpr fun hu => h ((isUnit_iff_ord_eq_zero v hf hf0).mp hu)

theorem ord_eq_zero_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  by_contra h'
  exact h (evalAt_eq_zero_of_ord_ne_zero v hv hf h')

theorem isUnit_of_evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra h'
  exact h ((evalAt_eq_zero_iff_not_isUnit v hv hf).mpr h')

theorem evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem evalAt_sub_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem v hv hf (neg_mem hg), evalAt_neg_of_mem v hv hg, ← sub_eq_add_neg]

theorem evalAt_pow_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih, pow_succ]

theorem evalAt_inv_of_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf0 := vsub_ne_zero_of_isUnit _ hf hu
  have hi := vsub_inv_mem v.toValuationSubring hf hu
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← v.evalAt_mul_of_mem hv hf hi, mul_inv_cancel₀ hf0, Place.evalAt_one]

theorem isUnit_pow_mk {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℕ) :
    IsUnit (⟨f ^ n, pow_mem hf n⟩ : v.toValuationSubring) := by
  have : (⟨f ^ n, pow_mem hf n⟩ : v.toValuationSubring) = ⟨f, hf⟩ ^ n := Subtype.ext (by simp)
  rw [this]
  exact hu.pow n

theorem zpow_mem_of_isUnit {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) : f ^ n ∈ v.toValuationSubring := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hf m
  · rw [zpow_negSucc]
    exact vsub_inv_mem _ _ (isUnit_pow_mk v hf hu (m + 1))

theorem evalAt_zpow_of_isUnit (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, evalAt_pow_of_mem v hv hf]
  · rw [zpow_negSucc, zpow_negSucc, ← evalAt_pow_of_mem v hv hf,
      evalAt_inv_of_isUnit v hv (pow_mem hf _) (isUnit_pow_mk v hf hu (m + 1))]

theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  apply (isUnit_iff_ord_eq_zero v (v.algebraMap_mem' c) hc').mp
  refine vsub_isUnit_of_inv_mem _ _ hc' ?_
  rw [← map_inv₀]
  exact v.algebraMap_mem' c⁻¹

theorem isUnit_algebraMap_mk {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
  (isUnit_iff_ord_eq_zero v _ ((map_ne_zero _).mpr hc)).mpr (ord_algebraMap v c)

theorem ord_smul_const {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) : v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap v, zero_add]

end PlaceHelpers

section Frame

variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  [IsCurveOver L F] [Algebra.EssFiniteType L F]
  {S : Set (Place L F)} {𝒩₀ : Subring F} [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
  {C : Subring L} {ϖ : ↥C} [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  {π : W} {σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀} {E : ℕ}
  {ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)}

structure DF (A : ValuationSubring L) (S : Set (Place L F)) (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (C : Subring L) (ϖ : ↥C) (π : W) (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)) : Prop where
  hrat : ∀ P ∈ S, P.IsRational
  hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)
  hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F)
  hC : ∀ c : L, c ∈ C → c ∈ A
  hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀
  hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d'
  hϖ0 : ((ϖ : ↥C) : L) ≠ 0
  halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a
  hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0
  hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n
  hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩)
  hπ : Irreducible π
  hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩
  hE : 1 ≤ E
  hconst : ∀ o : W, ι (σ o) = const (π ^ E) o

variable (H : DF A S 𝒩₀ C ϖ π σ E ι)
include H

noncomputable abbrev φ (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] {W : Type*} [CommRing W] {π : W} {E : ℕ}
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)) : ↥𝒩₀ →+* UVCrossingModel W (π ^ E) :=
  (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ →+* UVCrossingModel W (π ^ E)).comp
    (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀))

theorem memP {P : Place L F} (hP : P ∈ S) (g : ↥𝒩₀) : (g : F) ∈ P.toValuationSubring :=
  ((H.hS P).1 hP).1 (g : F) g.2

noncomputable def χ {P : Place L F} (hP : P ∈ S) : ↥𝒩₀ →+* L where
  toFun g := P.evalAt (g : F)
  map_one' := by
    have : ((1 : ↥𝒩₀) : F) = algebraMap L F 1 := by simp
    rw [this, Place.evalAt_algebraMap_eq]
  map_mul' a b := by
    rw [Subring.coe_mul]
    exact Place.evalAt_mul_of_mem (hv := H.hrat P hP) (hf := memP H hP a) (hg := memP H hP b)
  map_zero' := evalAt_zero' P
  map_add' a b := by
    rw [Subring.coe_add]
    exact evalAt_add_of_mem P (H.hrat P hP) (memP H hP a) (memP H hP b)

theorem χ_apply {P : Place L F} (hP : P ∈ S) (g : ↥𝒩₀) : χ H hP g = P.evalAt (g : F) := rfl

noncomputable def 𝔭of {P : Place L F} (hP : P ∈ S) : Ideal ↥𝒩₀ := RingHom.ker (χ H hP)

theorem mem_𝔭of_iff {P : Place L F} (hP : P ∈ S) (g : ↥𝒩₀) : g ∈ 𝔭of H hP ↔ P.evalAt (g : F) = 0 :=
  RingHom.mem_ker

scoped instance isPrime_𝔭of {P : Place L F} (hP : P ∈ S) : (𝔭of H hP).IsPrime := RingHom.ker_isPrime _

theorem over_𝔭of {P : Place L F} (hP : P ∈ S) : ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭of H hP :=
  fun g => (mem_𝔭of_iff H hP g).symm

noncomputable abbrev ϖN : ↥𝒩₀ := ⟨algebraMap L F (ϖ : L), H.hCmem ϖ ϖ.2⟩

theorem ϖN_not_mem_𝔭of {P : Place L F} (hP : P ∈ S) : ϖN H ∉ 𝔭of H hP := by
  rw [mem_𝔭of_iff]
  change P.evalAt (algebraMap L F (ϖ : L)) ≠ 0
  rw [Place.evalAt_algebraMap_eq]
  exact H.hϖ0

theorem mem_𝔭of_of_ord_ne_zero {P : Place L F} (hP : P ∈ S) {f : ↥𝒩₀} (hf0 : f ≠ 0) (h : P.ord (f : F) ≠ 0) :
    f ∈ 𝔭of H hP := by
  rw [mem_𝔭of_iff]
  exact evalAt_eq_zero_of_ord_ne_zero P (H.hrat P hP) (memP H hP f) h

theorem 𝔭of_ne_bot_of_ord_ne_zero {P : Place L F} (hP : P ∈ S) {f : ↥𝒩₀} (hf0 : f ≠ 0) (h : P.ord (f : F) ≠ 0) :
    𝔭of H hP ≠ ⊥ := fun hb => hf0 (by simpa [hb] using mem_𝔭of_of_ord_ne_zero H hP hf0 h)

end Frame

section Frame2

variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  [IsCurveOver L F] [Algebra.EssFiniteType L F]
  {S : Set (Place L F)} {𝒩₀ : Subring F} [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
  {C : Subring L} {ϖ : ↥C} [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  {π : W} {σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀} {E : ℕ}
  {ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)}
  (H : DF A S 𝒩₀ C ϖ π σ E ι)
include H

local notation "R" => UVCrossingModel W (π ^ E)

theorem φ_ϖN : φ 𝒩₀ ι (ϖN H) = const (π ^ E) π := by
  simp only [φ, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← H.hσπ, H.hconst]

theorem φ_injective : Function.Injective (φ 𝒩₀ ι) := by
  simp only [φ, RingHom.coe_comp, RingHom.coe_coe]
  refine ι.injective.comp ?_
  haveI : IsHausdorff (maximalIdeal ↥𝒩₀) ↥𝒩₀ := inferInstance
  exact AdicCompletion.of_injective (maximalIdeal ↥𝒩₀) ↥𝒩₀

theorem exists_comap_eq (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] : ∃ Q : PrimeSpectrum R, Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭 := by
  haveI := IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal ↥𝒩₀
  obtain ⟨Q', hQ'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := ↥𝒩₀)
    (B := AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨𝔭, inferInstance⟩
  refine ⟨PrimeSpectrum.comap (ι.symm : R →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) Q', ?_⟩
  have h1 : Ideal.comap (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)) Q'.asIdeal = 𝔭 := by
    simpa using congrArg PrimeSpectrum.asIdeal hQ'
  rw [← h1]
  ext g
  simp only [φ, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply, RingEquiv.symm_apply_apply]

theorem comap_horizontal {Q : PrimeSpectrum R} (hQ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal)
    {f : ↥𝒩₀} (hf0 : f ≠ 0) (hfQ : φ 𝒩₀ ι f ∈ Q.asIdeal) :
    Ideal.comap (φ 𝒩₀ ι) Q.asIdeal ≠ ⊥ ∧ ϖN H ∉ Ideal.comap (φ 𝒩₀ ι) Q.asIdeal ∧ f ∈ Ideal.comap (φ 𝒩₀ ι) Q.asIdeal := by
  refine ⟨fun hb => hf0 ?_, ?_, Ideal.mem_comap.mpr hfQ⟩
  · have : f ∈ Ideal.comap (φ 𝒩₀ ι) Q.asIdeal := Ideal.mem_comap.mpr hfQ
    rw [hb] at this
    simpa using this
  · rw [Ideal.mem_comap, φ_ϖN H]
    exact hQ.2

theorem horizontal_of_comap {Q : PrimeSpectrum R} {𝔭 : Ideal ↥𝒩₀} (h : Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭)
    (h0 : 𝔭 ≠ ⊥) (hϖ : ϖN H ∉ 𝔭) : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal := by
  constructor
  · intro hb
    apply h0
    rw [← h, hb]
    ext g
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun hg => φ_injective H (by simpa using hg), fun hg => by simp [hg]⟩
  · intro hm
    apply hϖ
    rw [← h, Ideal.mem_comap, φ_ϖN H]
    exact hm

end Frame2

section Frame3

variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  [IsCurveOver L F] [Algebra.EssFiniteType L F]
  {S : Set (Place L F)} {𝒩₀ : Subring F} [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
  {C : Subring L} {ϖ : ↥C} [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  {π : W} {σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀} {E : ℕ}
  {ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)}
  (H : DF A S 𝒩₀ C ϖ π σ E ι)
include H

local notation "R" => UVCrossingModel W (π ^ E)

def Over (S : Set (Place L F)) (𝒩₀ : Subring F) (𝔭 : Ideal ↥𝒩₀) : Set (Place L F) :=
  {P : Place L F | P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭}

omit H in
theorem mem_Over {𝔭 : Ideal ↥𝒩₀} {P : Place L F} : P ∈ Over S 𝒩₀ 𝔭 ↔ P ∈ S ∧ ∀ g : ↥𝒩₀, P.evalAt (g : F) = 0 ↔ g ∈ 𝔭 :=
  Iff.rfl

theorem mem_Over_iff {𝔭 : Ideal ↥𝒩₀} {P : Place L F} (hP : P ∈ S) : P ∈ Over S 𝒩₀ 𝔭 ↔ 𝔭of H hP = 𝔭 := by
  rw [mem_Over]
  constructor
  · rintro ⟨-, h⟩
    ext g
    rw [mem_𝔭of_iff]
    exact h g
  · rintro rfl
    exact ⟨hP, over_𝔭of H hP⟩

theorem mem_Over_𝔭of {P : Place L F} (hP : P ∈ S) : P ∈ Over S 𝒩₀ (𝔭of H hP) := (mem_Over_iff H hP).mpr rfl

theorem over_finite_and_ncard (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (hϖ : ϖN H ∉ 𝔭) :
    (Over S 𝒩₀ 𝔭).Finite ∧
    (((Over S 𝒩₀ 𝔭).ncard : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum R) (_ : Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭), (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) :=
  AlgebraicCurve.NodeAnnulusEngine.finite_and_ncard_eq_finsum_finrank_of_forall_iff_evalAt_eq_zero
    A S H.hrat 𝒩₀ H.hS H.hgen C H.hC H.hCmem ϖ H.hϖ H.hϖ0 H.halg H.hld H.hrk H.hres π H.hπ σ H.hσπ E H.hE ι H.hconst 𝔭 h0 hϖ

theorem toNat_ord_eq_length (𝔭 : Ideal ↥𝒩₀) [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (hϖ : ϖN H ∉ 𝔭)
    {P : Place L F} (hPo : P ∈ Over S 𝒩₀ 𝔭) (Q : PrimeSpectrum R) (hQ : Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭)
    (f : ↥𝒩₀) (hf0 : f ≠ 0) :
    ((P.ord (f : F)).toNat : ℕ∞) =
      Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (R ⧸ Ideal.span {ι (algebraMap ↥𝒩₀ _ f)})) :=
  AlgebraicCurve.NodeAnnulusEngine.toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero
    A S H.hrat 𝒩₀ H.hS H.hgen C H.hC H.hCmem ϖ H.hϖ H.hϖ0 H.halg H.hld H.hrk H.hres π H.hπ σ H.hσπ E H.hE ι H.hconst
    𝔭 h0 hϖ P hPo.1 hPo.2 Q hQ f hf0

theorem horF_finite (f : ↥𝒩₀) (hf0 : f ≠ 0) :
    {Q : PrimeSpectrum R | Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ φ 𝒩₀ ι f ∈ Q.asIdeal}.Finite :=
  ModularCurve.UVCrossingModel.setOf_horizontal_mem_finite π H.hπ E H.hE (φ 𝒩₀ ι f)
    (fun h => hf0 (φ_injective H (by simpa using h)))

end Frame3

section Frame4

variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  [IsCurveOver L F] [Algebra.EssFiniteType L F]
  {S : Set (Place L F)} {𝒩₀ : Subring F} [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
  {C : Subring L} {ϖ : ↥C} [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  {π : W} {σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀} {E : ℕ}
  {ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)}
  (H : DF A S 𝒩₀ C ϖ π σ E ι)
include H

local notation "R" => UVCrossingModel W (π ^ E)

noncomputable abbrev len (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E)) (f : ↥𝒩₀)
    (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) : ℕ∞ :=
  Module.length (Localization.AtPrime Q.asIdeal)
    (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥𝒩₀ _ f)}))

noncomputable abbrev rk (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) : ℕ∞ :=
  (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞)

omit H in

theorem len_eq_zero_of_not_mem (f : ↥𝒩₀) {Q : PrimeSpectrum R} (h : φ 𝒩₀ ι f ∉ Q.asIdeal) : len ι f Q = 0 := by
  rw [len, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  intro m
  refine ⟨φ 𝒩₀ ι f, h, ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  have : (φ 𝒩₀ ι f) • (Ideal.Quotient.mk (Ideal.span {ι (algebraMap ↥𝒩₀ _ f)}) r) =
      Ideal.Quotient.mk (Ideal.span {ι (algebraMap ↥𝒩₀ _ f)}) (φ 𝒩₀ ι f * r) := by
    rw [map_mul]; rfl
  rw [this, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem over_nonempty {Q₀ : PrimeSpectrum R} (hQ₀ : Q₀.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q₀.asIdeal)
    {f : ↥𝒩₀} (hf0 : f ≠ 0) (hfQ : φ 𝒩₀ ι f ∈ Q₀.asIdeal) :
    (Over S 𝒩₀ (Ideal.comap (φ 𝒩₀ ι) Q₀.asIdeal)).Nonempty := by
  set 𝔭 := Ideal.comap (φ 𝒩₀ ι) Q₀.asIdeal with h𝔭
  haveI : 𝔭.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨h0, hϖ, hf𝔭⟩ := comap_horizontal H hQ₀ hf0 hfQ
  obtain ⟨hfin, hcount⟩ := over_finite_and_ncard H 𝔭 h0 hϖ
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, Set.ncard_empty, Nat.cast_zero] at hcount

  have hsub : {Q : PrimeSpectrum R | Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭} ⊆
      {Q : PrimeSpectrum R | Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ φ 𝒩₀ ι f ∈ Q.asIdeal} := by
    intro Q hQ
    obtain ⟨h1, h2⟩ := horizontal_of_comap H hQ h0 hϖ
    refine ⟨h1, h2, ?_⟩
    have : f ∈ Ideal.comap (φ 𝒩₀ ι) Q.asIdeal := by rw [show Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭 from hQ]; exact hf𝔭
    exact Ideal.mem_comap.mp this
  have hfin' := (horF_finite H f hf0).subset hsub
  have hcount' : (0 : ℕ∞) = ∑ᶠ Q ∈ {Q : PrimeSpectrum R | Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭},
      (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) := hcount
  clear hcount
  have hcount := hcount'
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin'] at hcount
  have hQ₀mem : Q₀ ∈ hfin'.toFinset := by rw [Set.Finite.mem_toFinset]; exact rfl
  have hle : (Module.finrank W (R ⧸ Q₀.asIdeal) : ℕ∞) ≤
      ∑ Q ∈ hfin'.toFinset, (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) :=
    Finset.single_le_sum (f := fun Q : PrimeSpectrum R => (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞))
      (fun _ _ => zero_le') hQ₀mem
  rw [← hcount] at hle
  have h1 := (ModularCurve.UVCrossingModel.exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem
    π H.hπ E H.hE Q₀ hQ₀.1 hQ₀.2).1
  have : (1 : ℕ∞) ≤ 0 := le_trans (by exact_mod_cast h1) hle
  exact absurd this (by simp)

theorem main (f : ↥𝒩₀) (hf0 : f ≠ 0) :
    {P : Place L F | P ∈ S ∧ P.ord (f : F) ≠ 0}.Finite ∧
    ((∑ᶠ P ∈ S, (P.ord (f : F)).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal), rk Q * len ι f Q := by
  classical

  set HF : Set (PrimeSpectrum R) :=
    {Q : PrimeSpectrum R | Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ φ 𝒩₀ ι f ∈ Q.asIdeal} with hHF
  have hHFfin : HF.Finite := horF_finite H f hf0
  set cm : PrimeSpectrum R → Ideal ↥𝒩₀ := fun Q => Ideal.comap (φ 𝒩₀ ι) Q.asIdeal with hcm
  set Ps : Set (Ideal ↥𝒩₀) := cm '' HF with hPsdef
  have hPsfin : Ps.Finite := hHFfin.image cm

  have hHF_of_cm : ∀ {Q : PrimeSpectrum R} {𝔭 : Ideal ↥𝒩₀}, cm Q = 𝔭 → 𝔭 ≠ ⊥ → ϖN H ∉ 𝔭 → f ∈ 𝔭 → Q ∈ HF := by
    intro Q 𝔭 hQ h0 hϖ hf
    obtain ⟨h1, h2⟩ := horizontal_of_comap H hQ h0 hϖ
    refine ⟨h1, h2, ?_⟩
    have : f ∈ cm Q := hQ ▸ hf
    exact Ideal.mem_comap.mp this

  have hPs : ∀ 𝔭 ∈ Ps, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ϖN H ∉ 𝔭 ∧ f ∈ 𝔭 := by
    rintro 𝔭 ⟨Q, hQ, rfl⟩
    exact ⟨Ideal.IsPrime.comap _, comap_horizontal H ⟨hQ.1, hQ.2.1⟩ hf0 hQ.2.2⟩

  set U : Set (Place L F) := ⋃ 𝔭 ∈ Ps, Over S 𝒩₀ 𝔭 with hU
  have hUfin : U.Finite := by
    refine Set.Finite.biUnion hPsfin fun 𝔭 h𝔭 => ?_
    obtain ⟨hp, h0, hϖ, -⟩ := hPs 𝔭 h𝔭
    haveI := hp
    exact (over_finite_and_ncard H 𝔭 h0 hϖ).1
  have hUS : U ⊆ S := by
    intro P hP
    simp only [hU, Set.mem_iUnion] at hP
    obtain ⟨𝔭, -, hP⟩ := hP
    exact hP.1

  have hTU : {P : Place L F | P ∈ S ∧ P.ord (f : F) ≠ 0} ⊆ U := by
    rintro P ⟨hP, hord⟩
    have hf𝔭 : f ∈ 𝔭of H hP := mem_𝔭of_of_ord_ne_zero H hP hf0 hord
    obtain ⟨Q, hQ⟩ := exists_comap_eq H (𝔭of H hP)
    have hQHF : Q ∈ HF := hHF_of_cm hQ (𝔭of_ne_bot_of_ord_ne_zero H hP hf0 hord) (ϖN_not_mem_𝔭of H hP) hf𝔭
    simp only [hU, Set.mem_iUnion]
    exact ⟨𝔭of H hP, ⟨Q, hQHF, hQ⟩, mem_Over_𝔭of H hP⟩
  refine ⟨hUfin.subset hTU, ?_⟩

  set t : Place L F → ℕ := fun P => (P.ord (f : F)).toNat with ht
  set g : PrimeSpectrum R → ℕ∞ := fun Q => rk Q * len ι f Q with hg

  have hRHS : (∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal), g Q) =
      ∑ Q ∈ hHFfin.toFinset, g Q := by
    have : (∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal), g Q) =
        ∑ᶠ Q ∈ {Q : PrimeSpectrum R | Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal}, g Q := rfl
    rw [this]
    refine finsum_mem_eq_sum_of_inter_support_eq g ?_
    ext Q
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Set.Finite.coe_toFinset]
    constructor
    · rintro ⟨⟨h1, h2⟩, hne⟩
      refine ⟨⟨h1, h2, ?_⟩, hne⟩
      by_contra hnot
      exact hne (by simp [hg, len_eq_zero_of_not_mem f hnot])
    · rintro ⟨⟨h1, h2, -⟩, hne⟩
      exact ⟨⟨h1, h2⟩, hne⟩

  have hLHS : (∑ᶠ P ∈ S, t P) = ∑ P ∈ hUfin.toFinset, t P := by
    refine finsum_mem_eq_sum_of_inter_support_eq t ?_
    ext P
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset]
    constructor
    · rintro ⟨hP, hne⟩
      refine ⟨hTU ⟨hP, ?_⟩, hne⟩
      intro h0
      exact hne (by simp [ht, h0])
    · rintro ⟨hP, hne⟩
      exact ⟨hUS hP, hne⟩
  rw [hRHS, hLHS, Nat.cast_sum]

  set 𝔭of' : Place L F → Ideal ↥𝒩₀ := fun P => if hP : P ∈ S then 𝔭of H hP else ⊥ with h𝔭of'
  have h𝔭of'_eq : ∀ {P : Place L F} (hP : P ∈ S), 𝔭of' P = 𝔭of H hP := fun hP => by simp [h𝔭of', hP]
  have hmapsL : ∀ P ∈ hUfin.toFinset, 𝔭of' P ∈ hPsfin.toFinset := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP ⊢
    simp only [hU, Set.mem_iUnion] at hP
    obtain ⟨𝔭, h𝔭, hPo⟩ := hP
    rwa [h𝔭of'_eq hPo.1, (mem_Over_iff H hPo.1).mp hPo]
  have hmapsR : ∀ Q ∈ hHFfin.toFinset, cm Q ∈ hPsfin.toFinset := by
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ ⊢
    exact ⟨Q, hQ, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmapsL, ← Finset.sum_fiberwise_of_maps_to hmapsR]
  refine Finset.sum_congr rfl fun 𝔭 h𝔭 => ?_
  rw [Set.Finite.mem_toFinset] at h𝔭
  obtain ⟨hp, h0, hϖ, hf𝔭⟩ := hPs 𝔭 h𝔭
  haveI := hp
  obtain ⟨Q₀, hQ₀HF, hQ₀⟩ := h𝔭
  obtain ⟨hOfin, hOcount⟩ := over_finite_and_ncard H 𝔭 h0 hϖ
  obtain ⟨P₀, hP₀⟩ := over_nonempty H ⟨hQ₀HF.1, hQ₀HF.2.1⟩ hf0 hQ₀HF.2.2
  rw [show Ideal.comap (φ 𝒩₀ ι) Q₀.asIdeal = 𝔭 from hQ₀] at hP₀

  have hlen : ∀ Q : PrimeSpectrum R, cm Q = 𝔭 → len ι f Q = ((P₀.ord (f : F)).toNat : ℕ∞) :=
    fun Q hQ => (toNat_ord_eq_length H 𝔭 h0 hϖ hP₀ Q hQ f hf0).symm

  have hord : ∀ P : Place L F, P ∈ Over S 𝒩₀ 𝔭 → ((t P : ℕ) : ℕ∞) = ((P₀.ord (f : F)).toNat : ℕ∞) := by
    intro P hPo
    rw [ht]
    simp only
    rw [toNat_ord_eq_length H 𝔭 h0 hϖ hPo Q₀ hQ₀ f hf0]
    exact hlen Q₀ hQ₀

  have hfibL : (hUfin.toFinset.filter fun P => 𝔭of' P = 𝔭) = hOfin.toFinset := by
    ext P
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hPU, hP𝔭⟩
      have hPS := hUS hPU
      rw [h𝔭of'_eq hPS] at hP𝔭
      exact (mem_Over_iff H hPS).mpr hP𝔭
    · intro hPo
      refine ⟨?_, ?_⟩
      · simp only [hU, Set.mem_iUnion]
        exact ⟨𝔭, ⟨Q₀, hQ₀HF, hQ₀⟩, hPo⟩
      · rw [h𝔭of'_eq hPo.1]
        exact (mem_Over_iff H hPo.1).mp hPo

  have hL : (∑ P ∈ hUfin.toFinset.filter (fun P => 𝔭of' P = 𝔭), ((t P : ℕ) : ℕ∞)) =
      ((Over S 𝒩₀ 𝔭).ncard : ℕ∞) * ((P₀.ord (f : F)).toNat : ℕ∞) := by
    rw [hfibL, Finset.sum_congr rfl fun P hP => hord P ((Set.Finite.mem_toFinset _).mp hP), Finset.sum_const,
      nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hOfin]

  have hfibR : ((hHFfin.toFinset.filter fun Q => cm Q = 𝔭 : Finset (PrimeSpectrum R)) : Set (PrimeSpectrum R)) =
      {Q : PrimeSpectrum R | Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭} := by
    ext Q
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hHF_of_cm h h0 hϖ hf𝔭, h⟩⟩
  have hR : (∑ Q ∈ hHFfin.toFinset.filter (fun Q => cm Q = 𝔭), g Q) =
      (∑ᶠ (Q : PrimeSpectrum R) (_ : Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭), rk Q) * ((P₀.ord (f : F)).toNat : ℕ∞) := by
    have : (∑ᶠ (Q : PrimeSpectrum R) (_ : Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭), rk Q) =
        ∑ᶠ Q ∈ {Q : PrimeSpectrum R | Ideal.comap (φ 𝒩₀ ι) Q.asIdeal = 𝔭}, rk Q := rfl
    rw [this, ← hfibR, finsum_mem_coe_finset, Finset.sum_mul]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [Finset.mem_filter] at hQ
    rw [hg]
    simp only
    rw [hlen Q hQ.2]
  rw [hL, hR, hOcount]

end Frame4

end AlgebraicCurve.NodeAnnulusEngine.DictAssembly
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve.NodeAnnulusEngine P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve.NodeAnnulusEngine.DictAssembly"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve.NodeAnnulusEngine"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel.AlgebraicCurve"

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))

    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (f : ↥𝒩₀) (hf0 : f ≠ 0) :
    {P : Place L F | P ∈ S ∧ P.ord (f : F) ≠ 0}.Finite ∧
    ((∑ᶠ P ∈ S, (P.ord (f : F)).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap ↥𝒩₀ _ f)})) := by
  exact AlgebraicCurve.NodeAnnulusEngine.DictAssembly.main
    (⟨hrat, hS, hgen, hC, hCmem, hϖ, hϖ0, halg, hld, hrk, hres, hπ, hσπ, hE, hconst⟩ :
      AlgebraicCurve.NodeAnnulusEngine.DictAssembly.DF A S 𝒩₀ C ϖ π σ E ι) f hf0

end S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_finite_and_finsum_ord_eq_finsum_finrank_mul_length_of_ringEquiv_uvCrossingModel (solution)
