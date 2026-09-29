-- Prove2me | solution 1 for AlgebraicCurve.Place.mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e853da9c-5f2f-5b5e-9d2e-cab5ff4c02e9

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord.AlgebraicCurve KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.diffCoeff Place Place.coe_algebraMap Place.ord_mul Place.ord_inv Place.ord_zpow Place.residueInv_algebraMap Place.evalAt_of_mem Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "diffCoeff uniformizer_alt ext coe_algebraMap ResidueField ord ord_mul ord_inv ord_coe_unit ord_zpow toValuationSubring residueInv_algebraMap evalAt evalAt_of_mem diffCoeff_smul_D_of_ord_eq_one diffCoeff_smul_D_eq_of_ord_eq_one ord_diffCoeff_D_nonneg_of_perfectField mem_iff_ord_nonneg"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section LogDeriv

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_derivation_mul_div_mul (δ : Derivation K F F) (t : F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    t * δ (f * g) / (f * g) = t * δ f / f + t * δ g / g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

theorem mul_derivation_inv_div_inv (δ : Derivation K F F) (t : F) {f : F} (hf : f ≠ 0) :
    t * δ f⁻¹ / f⁻¹ = -(t * δ f / f) := by
  have h := mul_derivation_mul_div_mul δ t hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, Derivation.map_one_eq_zero, mul_zero, zero_div] at h
  linear_combination -h

theorem mul_derivation_zpow_div_zpow (δ : Derivation K F F) (t : F) {a : F} (ha : a ≠ 0) (n : ℤ) :
    t * δ (a ^ n) / a ^ n = (n : F) * (t * δ a / a) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one₀ ha, mul_derivation_mul_div_mul δ t (zpow_ne_zero _ ha) ha, ih]
    push_cast
    ring
  | pred n ih =>
    rw [zpow_sub_one₀ ha, mul_derivation_mul_div_mul δ t (zpow_ne_zero _ ha) (inv_ne_zero ha),
      mul_derivation_inv_div_inv δ t ha, ih]
    push_cast
    ring

end LogDeriv

section DerivOfUniformizer

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]

theorem diffCoeff_eq_of_eq_smul_D_of_ord_eq_one (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) {ω : Ω[F⁄K]} {g : F}
    (h : ω = g • KaehlerDifferential.D K F t) :
    diffCoeff t ω = g := by
  rw [h]
  exact diffCoeff_smul_D_eq_of_ord_eq_one x v ht g

noncomputable def derivationOfOrdEqOne (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) : Derivation K F F where
  toFun f := diffCoeff t (KaehlerDifferential.D K F f)
  map_add' f g := by
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [map_add, add_smul, diffCoeff_smul_D_of_ord_eq_one x v ht,
      diffCoeff_smul_D_of_ord_eq_one x v ht]
  map_smul' a f := by
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [Derivation.map_smul, RingHom.id_apply, smul_assoc, diffCoeff_smul_D_of_ord_eq_one x v ht]
  map_one_eq_zero' := by
    show diffCoeff t (KaehlerDifferential.D K F 1) = 0
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [Derivation.map_one_eq_zero, zero_smul]
  leibniz' f g := by
    show diffCoeff t (KaehlerDifferential.D K F (f * g)) =
      f • diffCoeff t (KaehlerDifferential.D K F g) + g • diffCoeff t (KaehlerDifferential.D K F f)
    refine diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht ?_
    rw [Derivation.leibniz, add_smul, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul,
      diffCoeff_smul_D_of_ord_eq_one x v ht, diffCoeff_smul_D_of_ord_eq_one x v ht]

theorem derivationOfOrdEqOne_apply (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (f : F) :
    derivationOfOrdEqOne x v ht f = diffCoeff t (KaehlerDifferential.D K F f) := rfl

theorem derivationOfOrdEqOne_self (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) :
    derivationOfOrdEqOne x v ht t = 1 :=
  diffCoeff_eq_of_eq_smul_D_of_ord_eq_one x v ht (one_smul F _).symm

theorem derivationOfOrdEqOne_mem (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) {f : F} (hf : f ∈ v.toValuationSubring) :
    derivationOfOrdEqOne x v ht f ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0, map_zero]; exact zero_mem _
  by_cases hd : derivationOfOrdEqOne x v ht f = 0
  · rw [hd]; exact zero_mem _
  rw [mem_iff_ord_nonneg v hd, derivationOfOrdEqOne_apply]
  exact ord_diffCoeff_D_nonneg_of_perfectField x v ht ((mem_iff_ord_nonneg v hf0).mp hf)

end DerivOfUniformizer

end AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) {f : F} (hf : f ≠ 0) :
    t * Place.diffCoeff t (KaehlerDifferential.D K F f) / f ∈ v.toValuationSubring ∧
      v.evalAt (t * Place.diffCoeff t (KaehlerDifferential.D K F f) / f) = ((v.ord f : ℤ) : K) := by
  obtain ⟨δ, hδ, hδt, hδmem⟩ : ∃ δ : Derivation K F F,
      (∀ g : F, δ g = Place.diffCoeff t (KaehlerDifferential.D K F g)) ∧ δ t = 1 ∧
        ∀ g : F, g ∈ v.toValuationSubring → δ g ∈ v.toValuationSubring :=
    ⟨Place.derivationOfOrdEqOne x v ht, fun _ => rfl, Place.derivationOfOrdEqOne_self x v ht,
      fun _ hg => Place.derivationOfOrdEqOne_mem x v ht hg⟩
  rw [← hδ f]
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have htmem : t ∈ v.toValuationSubring := (Place.mem_iff_ord_nonneg v ht0).mpr (by omega)

  set m : ℤ := v.ord f with hm
  have hw0 : f * t ^ (-m) ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ ht0)
  have hordw : v.ord (f * t ^ (-m)) = 0 := by
    rw [Place.ord_mul _ hf (zpow_ne_zero _ ht0), Place.ord_zpow, ht]; ring
  have hwmem : f * t ^ (-m) ∈ v.toValuationSubring :=
    (Place.mem_iff_ord_nonneg v hw0).mpr hordw.ge
  have hwinv : (f * t ^ (-m))⁻¹ ∈ v.toValuationSubring :=
    (Place.mem_iff_ord_nonneg v (inv_ne_zero hw0)).mpr (by rw [Place.ord_inv, hordw, neg_zero])
  have hδw : δ (f * t ^ (-m)) ∈ v.toValuationSubring := hδmem _ hwmem
  have hf_eq : f = (f * t ^ (-m)) * t ^ m := by
    rw [mul_assoc, ← zpow_add₀ ht0, neg_add_cancel, zpow_zero, mul_one]
  have halg : algebraMap K F (m : K) ∈ v.toValuationSubring := by
    rw [← Place.coe_algebraMap]; exact SetLike.coe_mem _

  have key : t * δ f / f = t * (δ (f * t ^ (-m)) * (f * t ^ (-m))⁻¹) + algebraMap K F (m : K) := by
    conv_lhs => rw [hf_eq]
    rw [Place.mul_derivation_mul_div_mul δ t hw0 (zpow_ne_zero m ht0),
      Place.mul_derivation_zpow_div_zpow δ t ht0 m, hδt, map_intCast]
    field_simp
  have hmem : t * (δ (f * t ^ (-m)) * (f * t ^ (-m))⁻¹) + algebraMap K F (m : K) ∈ v.toValuationSubring :=
    add_mem (mul_mem htmem (mul_mem hδw hwinv)) halg
  rw [key]
  refine ⟨hmem, ?_⟩
  rw [Place.evalAt_of_mem v hmem]

  have htunit : ¬ IsUnit (⟨t, htmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    rw [ht] at this
    exact one_ne_zero this
  have hres_t : IsLocalRing.residue v.toValuationSubring ⟨t, htmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr htunit)
  have helt : (⟨_, hmem⟩ : v.toValuationSubring) =
      ⟨t, htmem⟩ * (⟨_, hδw⟩ * ⟨_, hwinv⟩) + algebraMap K v.toValuationSubring (m : K) :=
    Subtype.ext rfl
  rw [helt, map_add, map_mul, hres_t, zero_mul, zero_add]
  have hsc : IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring (m : K)) =
      algebraMap K v.ResidueField (m : K) := rfl
  rw [hsc, Place.residueInv_algebraMap]

end S_AlgebraicCurve_Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
end P2MW
export P2MW.S_AlgebraicCurve_Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord (solution)
