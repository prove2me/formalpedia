-- Prove2me | solution 1 for AlgebraicCurve.weilReciprocity_algebraMap_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/42b5d75a-e188-5da2-b33e-3bd494412902

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Divisor_pushforward_div_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_weilReciprocity_algebraMap_of_isSeparable
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F] [HasPrincipalDivisors K F'] (hbase : WeilReciprocity K F) {f : F'} {g : F} (hf : f ≠ 0) (hg : g ≠ 0) (Df Dg : Divisor K F') (hDf : ∀ w : Place K F', Df w = w.ord f) (hDg : ∀ w : Place K F', Dg w = w.ord (algebraMap F F' g)) (hdisj : ∀ w : Place K F', w.ord f = 0 ∨ w.ord (algebraMap F F' g) = 0) (hratf : ∀ w ∈ Df.support, Place.IsRational w) (hratF : ∀ v : Place K F, v.IsRational) (hratfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', Place.IsRational w) : Divisor.evalFun f Dg = Divisor.evalFun (algebraMap F F' g) Df := by
  classical
  have hNf : Algebra.norm F f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  obtain ⟨Eg, hEg, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  obtain ⟨EN, hEN, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (Algebra.norm F f) hNf
  have hfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', w.ord f = 0 := by
    intro v hv w hw
    refine (hdisj w).resolve_right ?_
    rw [w.ord_restrict (F := F) g, Place.mem_fiber.mp hw]
    have hepos := w.ramificationIndex_pos (F := F)
    exact mul_ne_zero (by exact_mod_cast hepos.ne') hv
  have hres : ∀ w : Place K F', w.ord f ≠ 0 → (w.restrict F).ord g = 0 := by
    intro w hw
    have hzero := (hdisj w).resolve_left hw
    rw [w.ord_restrict (F := F) g] at hzero
    have hepos := w.ramificationIndex_pos (F := F)
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (by exact_mod_cast hepos.ne')
    · exact h
  have hdisjF : ∀ v : Place K F, v.ord (Algebra.norm F f) = 0 ∨ v.ord g = 0 := by
    intro v
    rcases eq_or_ne (v.ord g) 0 with h | h
    · exact Or.inr h
    · exact Or.inl (AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber_of_isSeparable hf v (hfib v h))
  have hstep1 : Dg = Divisor.pullback F' Eg := by
    ext w
    rw [hDg w, Divisor.pullback_apply_eq_ord (fun u => hEg u)]
  have hstep4 : Divisor.pushforward F Df = EN :=
    AlgebraicCurve.Divisor.pushforward_div_of_isSeparable hf hDf hEN
  have hstep2 : Divisor.evalFun f (Divisor.pullback F' Eg)
      = Divisor.evalFun (Algebra.norm F f) Eg := by
    refine AlgebraicCurve.Divisor.evalFun_pullback hf Eg (fun v _ => hratF v) (fun v hv w hw => ?_)
      (fun v hv w hw => ?_)
    · exact hratfib v (by rw [← hEg v]; exact Finsupp.mem_support_iff.mp hv) w hw
    · exact hfib v (by rw [← hEg v]; exact Finsupp.mem_support_iff.mp hv) w hw
  have hstep3 : Divisor.evalFun (Algebra.norm F f) Eg = Divisor.evalFun g EN :=
    hbase (Algebra.norm F f) g EN Eg hNf hg hEN hEg hdisjF
      (fun v _ => hratF v) (fun v _ => hratF v)
  have hstep5 : Divisor.evalFun (algebraMap F F' g) Df
      = Divisor.evalFun g (Divisor.pushforward F Df) := by
    refine AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward hg Df (fun w hw => hratf w hw)
      (fun w _ => hratF _) (fun w hw => ?_)
    exact hres w (by rw [← hDf w]; exact Finsupp.mem_support_iff.mp hw)
  rw [hstep1, hstep2, hstep3, ← hstep4, ← hstep5]

end S_AlgebraicCurve_weilReciprocity_algebraMap_of_isSeparable
end P2MW
export P2MW.S_AlgebraicCurve_weilReciprocity_algebraMap_of_isSeparable (solution)
