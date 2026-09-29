-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_ord_sub_algebraMap_pos_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fb4b6949-2ade-5b7c-a3db-f15878f30f83

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField

namespace POV

theorem transcendental_sub_algebraMap {K M : Type*} [Field K] [Field M] [Algebra K M] {t : M} (ht : Transcendental K t) (c : K) :
    Transcendental K (t - algebraMap K M c) := by
  intro halg
  apply ht
  have : t = (t - algebraMap K M c) + algebraMap K M c := by ring
  rw [this]
  exact halg.add (isAlgebraic_algebraMap c)

theorem not_isUnit_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M] {f : M} (hf : Transcendental K f) :
    ¬ IsUnit (⟨f, Algebra.subset_adjoin (Set.mem_singleton f)⟩ : Algebra.adjoin K ({f} : Set M)) := by
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv

  have hgmem : (g : M) ∈ (Polynomial.aeval (R := K) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval K f]; exact g.2
  obtain ⟨q, hq⟩ := hgmem
  have hinj : Function.Injective (Polynomial.aeval (R := K) f) := transcendental_iff_injective.mp hf
  have h1 : Polynomial.aeval (R := K) f (Polynomial.X * q) = Polynomial.aeval (R := K) f 1 := by
    rw [map_mul, Polynomial.aeval_X, map_one, show Polynomial.aeval f q = (g : M) from hq]
    exact congrArg Subtype.val hg
  have h2 : (Polynomial.X * q : Polynomial K) = 1 := hinj h1
  have h3 : IsUnit (Polynomial.X : Polynomial K) := IsUnit.of_mul_eq_one _ h2
  exact Polynomial.not_isUnit_X h3

end POV

open POV in
theorem solution {K M : Type*} [Field K] [Field M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [Algebra.IsSeparable K⟮t⟯ M] (c : K) :
    ∃ v : AlgebraicCurve.Place K M, 0 < v.ord (t - algebraMap K M c) := by
  classical
  set f : M := t - algebraMap K M c with hfdef
  have hf : Transcendental K f := transcendental_sub_algebraMap ht c
  have hf0 : f ≠ 0 := fun h => hf (by rw [h]; exact isAlgebraic_zero)

  let R : Subring M := (Algebra.adjoin K ({f} : Set M)).toSubring
  let fR : R := ⟨f, Algebra.subset_adjoin (Set.mem_singleton f)⟩
  have hfR : ¬ IsUnit fR := not_isUnit_of_transcendental hf
  obtain ⟨𝔭, h𝔭max, hf𝔭⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hfR)
  haveI : 𝔭.IsPrime := h𝔭max.isPrime

  let L : LocalSubring M := LocalSubring.ofPrime R 𝔭
  obtain ⟨B, hB⟩ := L.exists_le_valuationSubring
  obtain ⟨hLB, hloc⟩ := LocalSubring.le_def.mp hB

  have hfL : ¬ IsUnit (algebraMap R L.toSubring fR) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff L.toSubring 𝔭 fR]
    exact fun h => h hf𝔭
  have hfLval : ((algebraMap R L.toSubring fR : L.toSubring) : M) = f := rfl
  have hfB_mem : f ∈ B := by
    have : ((algebraMap R L.toSubring fR : L.toSubring) : M) ∈ B.toSubring := hLB (algebraMap R L.toSubring fR).2
    exact this
  have hfB : ¬ IsUnit (⟨f, hfB_mem⟩ : B) := by
    intro hu
    apply hfL
    have hincl : Subring.inclusion hLB (algebraMap R L.toSubring fR) = ⟨f, hfB_mem⟩ := Subtype.ext hfLval
    haveI := hloc
    exact (isUnit_map_iff (Subring.inclusion hLB) _).mp (hincl ▸ hu)

  have hBK : ∀ a : K, algebraMap K M a ∈ B := by
    intro a
    have haR : algebraMap K M a ∈ R := (Algebra.adjoin K ({f} : Set M)).algebraMap_mem a
    have : ((algebraMap R L.toSubring ⟨_, haR⟩ : L.toSubring) : M) ∈ B.toSubring := hLB (algebraMap R L.toSubring ⟨_, haR⟩).2
    exact this
  have hBtop : B ≠ ⊤ := by
    intro htop
    apply hfB
    have : IsUnit f := isUnit_iff_ne_zero.mpr hf0

    refine ⟨⟨⟨f, hfB_mem⟩, ⟨f⁻¹, by rw [htop]; trivial⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable t B hBK hBtop
  refine ⟨v, ?_⟩

  have hfv : f ∈ v.toValuationSubring := hv ▸ hfB_mem
  have h0 : 0 ≤ v.ord f := (v.mem_iff_ord_nonneg hf0).mp hfv
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hinv : f⁻¹ ∈ v.toValuationSubring := by
      rw [v.mem_iff_ord_nonneg (inv_ne_zero hf0), v.ord_inv, ← h, neg_zero]
    apply hfB
    have hinvB : f⁻¹ ∈ B := hv ▸ hinv
    exact ⟨⟨⟨f, hfB_mem⟩, ⟨f⁻¹, hinvB⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩

end S_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental (solution)
