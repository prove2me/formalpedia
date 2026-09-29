-- Prove2me | solution 1 for AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a2ea35e1-c39b-5ca3-bf3c-51b777886975

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open AlgebraicCurve

theorem solution
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
    [Algebra F F₁] [Algebra F F₂] [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z']
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F Z] [IsScalarTower K F Z']
    [IsScalarTower K F₁ Z] [IsScalarTower K F₂ Z] [IsScalarTower K F₁ Z'] [IsScalarTower K F₂ Z']
    [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₂ Z] [FiniteDimensional F₁ Z'] [FiniteDimensional F₂ Z']
    [CharZero F]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (w₁ : Place K F₁) (w₂ : Place K F₂) (hw : w₁.restrict F = w₂.restrict F)
    (T : Finset (Place K Z)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂)
    (T' : Finset (Place K Z')) (hT' : ∀ W, W ∈ T' ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
        + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂
      = w₁.inertiaDeg F * w₂.ramificationIndex F := by
  classical

  haveI : PerfectField F := PerfectField.ofCharZero
  haveI : CharZero F₁ := charZero_of_injective_algebraMap (algebraMap F F₁).injective
  haveI : CharZero F₂ := charZero_of_injective_algebraMap (algebraMap F F₂).injective
  haveI : PerfectField F₂ := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable F F₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable F₂ Z := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable F₂ Z' := Algebra.IsAlgebraic.isSeparable_of_perfectField

  have hrr : ∀ W : Place K Z, (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  have hrr' : ∀ W : Place K Z', (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  set v : Place K F := w₁.restrict F with hv

  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq (v.fiberOver F₁)
    (fun w => if w = w₁ then (1 : ℤ) else 0)
  have hg1 : w₁.ord g = 1 := by
    have := hg w₁ ((Place.mem_fiberOver _).mpr rfl)
    simpa using this
  have hgz : ∀ w ∈ v.fiberOver F₁, w ≠ w₁ → w.ord g = 0 := fun w hw hne => by
    have := hg w hw
    simpa [hne] using this
  have hgZ : algebraMap F₁ Z g ≠ 0 := by simpa using hg0
  have hgZ' : algebraMap F₁ Z' g ≠ 0 := by simpa using hg0

  have hN := Algebra.algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top hgen hgen' hdeg hne g

  have h1 : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = (w₂.ramificationIndex F : ℤ) * (w₁.inertiaDeg F : ℤ) := by
    rw [Place.ord_restrict, ← hw, Place.ord_norm_eq_sum_fiberOver (w₁.restrict F) hg0,
      Finset.sum_eq_single_of_mem w₁ ((Place.mem_fiberOver _).mpr rfl)]
    · rw [hg1, mul_one]
    · intro w hw hne
      rw [hgz w hw hne, mul_zero]

  have h2 : w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z g))
      = ∑ W ∈ T, ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    rw [Place.ord_norm_eq_sum_fiberOver w₂ hgZ]
    have hTeq : T = (w₂.fiberOver Z).filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT, Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [if_pos h, h, hg1, mul_one, mul_comm]
    · rw [if_neg h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr, hW, ← hw]
  have h3 : w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z' g))
      = ∑ W ∈ T', ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    rw [Place.ord_norm_eq_sum_fiberOver w₂ hgZ']
    have hTeq : T' = (w₂.fiberOver Z').filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT', Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [if_pos h, h, hg1, mul_one, mul_comm]
    · rw [if_neg h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr', hW, ← hw]

  have hprod : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z g)) + w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z' g)) := by
    rw [hN, Place.ord_mul _ (Algebra.norm_ne_zero_iff.mpr hgZ) (Algebra.norm_ne_zero_iff.mpr hgZ')]
  rw [h1, h2, h3] at hprod
  have : ((∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
      + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂ : ℕ) : ℤ)
      = ((w₁.inertiaDeg F * w₂.ramificationIndex F : ℕ) : ℤ) := by
    push_cast
    rw [← hprod, mul_comm]
  exact_mod_cast this

end S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add
end P2MW
export P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add (solution)
