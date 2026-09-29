-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/73624fce-ff90-5cb5-9036-dc5daa51fa3d

import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Separable
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open AlgebraicCurve

namespace BifibreWEX

theorem restrict_restrict {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end BifibreWEX

theorem solution
    {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
    [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]
    (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E)
    (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (ha' : a'.toRingHom.IsIntegral) (hb' : b'.toRingHom.IsIntegral)
    (hsq : b'.comp b = a'.comp a)
    (hfin : FiniteAlong K (a'.comp a)) (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) =
      Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D) := by
  classical

  letI : Algebra F A := algebraAlong a
  letI : Algebra F B := algebraAlong b
  letI : Algebra A E := algebraAlong a'
  letI : Algebra B E := algebraAlong b'
  letI : Algebra F E := algebraAlong (a'.comp a)
  haveI : IsScalarTower K F A := isScalarTower_along a
  haveI : IsScalarTower K F B := isScalarTower_along b
  haveI : IsScalarTower K A E := isScalarTower_along a'
  haveI : IsScalarTower K B E := isScalarTower_along b'
  haveI : IsScalarTower K F E := isScalarTower_along (a'.comp a)
  haveI : IsScalarTower F A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F B E :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hsq x).symm
  haveI : Algebra.IsIntegral F A := isIntegral_along a ha
  haveI : Algebra.IsIntegral F B := isIntegral_along b hb
  haveI : Algebra.IsIntegral A E := isIntegral_along a' ha'
  haveI : Algebra.IsIntegral B E := isIntegral_along b' hb'

  haveI : Module.Finite F E := hfin
  haveI : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  haveI : Algebra.IsSeparable F E := hsep
  haveI : FiniteDimensional A E := Module.Finite.of_restrictScalars_finite F A E
  haveI : FiniteDimensional B E := Module.Finite.of_restrictScalars_finite F B E
  haveI : FiniteDimensional F A := Module.Finite.left F A E
  haveI : FiniteDimensional F B := Module.Finite.left F B E

  have hgenF : Algebra.adjoin F (Set.range (algebraMap A E) ∪ Set.range (algebraMap B E)) = ⊤ := by
    have hs : Set.range (algebraMap A E) ∪ Set.range (algebraMap B E) =
        Set.range a' ∪ Set.range b' := rfl
    rw [hs, eq_top_iff]
    intro z _
    have hz : z ∈ Algebra.adjoin K (Set.range a' ∪ Set.range b') := hgen ▸ Algebra.mem_top
    have hle : Algebra.adjoin K (Set.range a' ∪ Set.range b') ≤
        (Algebra.adjoin F (Set.range a' ∪ Set.range b')).restrictScalars K :=
      Algebra.adjoin_le fun x hx =>
        (Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin hx)
    exact (Subalgebra.mem_restrictScalars K).mp (hle hz)

  have eA : ∀ W : Place K E, Place.ramificationIndexAlong a' W = W.ramificationIndex A :=
    fun _ => rfl
  have fB : ∀ W : Place K E, W.inertiaDegAlong b' hb' = W.inertiaDeg B := fun _ => rfl
  have fF : ∀ w : Place K A, w.inertiaDegAlong a ha = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K B, Place.ramificationIndexAlong b w = w.ramificationIndex F :=
    fun _ => rfl

  suffices h : (Divisor.pullbackAlong b hb).comp (Divisor.pushforwardAlong a ha) =
      (Divisor.pushforwardAlong b' hb').comp (Divisor.pullbackAlong a' ha') from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    map_sum]
  simp only [Divisor.pushforwardAlong_single]

  ext wB
  rw [Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eA, fB, fF, eF]
  by_cases hv : wB.restrictAlong b hb = wA.restrictAlong a ha
  ·
    rw [if_pos (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong a' ha' wA).filter (fun W => W.restrictAlong b' hb' = wB)
        ↔ W.restrict A = wA ∧ W.restrict B = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
      (K := K) (F := F) (F₁ := A) (F₂ := B) (E := E) hgenF hLD (wA.restrictAlong a ha) wA wB
      rfl hv _ hT
    rw [Finset.sum_congr rfl fun W _ => mul_assoc n _ _, ← Finset.mul_sum, mul_assoc]
    congr 1
    exact_mod_cast key.symm
  ·
    rw [if_neg (fun h => hv (Place.mem_fiberAlong.mp h))]
    symm
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [if_neg]
    intro hWB
    apply hv
    have h₁ : W.restrict A = wA := Place.mem_fiberAlong.mp hW
    have h₂ : W.restrict B = wB := hWB
    show wB.restrict F = wA.restrict F
    rw [← h₁, ← h₂, BifibreWEX.restrict_restrict, BifibreWEX.restrict_restrict]

end S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong (solution)
