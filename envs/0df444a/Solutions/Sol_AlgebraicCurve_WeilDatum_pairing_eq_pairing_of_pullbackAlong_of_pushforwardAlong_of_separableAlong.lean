-- Prove2me | solution 1 for AlgebraicCurve.WeilDatum.pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8ab6dffa-6bfa-565c-862c-9a5f25584613

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_Isogeny_ConditionalCurrency
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

open AlgebraicCurve

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Ws23WeilAdj

open AlgebraicCurve

theorem main
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u) (hsep : SeparableAlong K u)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {n : ℕ} (d : WeilDatum K F' n) (d₀ : WeilDatum K F n)
    (hD₁ : d.D₁ = Divisor.pullbackAlong u hu d₀.D₁) (hf₁ : d.f₁ = u d₀.f₁)
    (hD₂ : d₀.D₂ = Divisor.pushforwardAlong u hu d.D₂)
    (hf₂ : d₀.f₂ = (letI := algebraAlong u; Algebra.norm F d.f₂)) :
    d.pairing = d₀.pairing := by
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep

  have hD₁w : ∀ w : Place K F', d.D₁ w = w.ramificationIndex F * d₀.D₁ (w.restrict F) := by
    intro w
    rw [hD₁]
    exact Divisor.pullback_apply d₀.D₁ w

  have hnum : Divisor.evalFun d.f₁ d.D₂ = Divisor.evalFun d₀.f₁ d₀.D₂ := by
    rw [hf₁, hD₂]
    refine Divisor.evalFun_algebraMap_pushforward d₀.f₁_ne_zero d.D₂ (fun w _ => hratF' w)
      (fun w _ => hratF _) (fun w hw => ?_)

    have h2 : d.D₂ w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have h1 : d.D₁ w = 0 := (d.disjoint w).resolve_right h2
    rw [hD₁w w] at h1
    have he : (w.ramificationIndex F : ℤ) ≠ 0 := by
      have := w.ramificationIndex_pos (F := F)
      exact_mod_cast this.ne'
    have h0 : d₀.D₁ (w.restrict F) = 0 := (mul_eq_zero.mp h1).resolve_left he
    rw [d₀.ord_f₁, h0, mul_zero]

  have hden : Divisor.evalFun d.f₂ d.D₁ = Divisor.evalFun d₀.f₂ d₀.D₁ := by
    rw [hD₁, hf₂]
    refine Divisor.evalFun_pullback d.f₂_ne_zero d₀.D₁ (fun v _ => hratF v)
      (fun v _ w _ => hratF' w) (fun v hv w hw => ?_)

    have hwv : w.restrict F = v := Place.mem_fiber.mp hw
    have hv' : d₀.D₁ v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have he : (w.ramificationIndex F : ℤ) ≠ 0 := by
      have := w.ramificationIndex_pos (F := F)
      exact_mod_cast this.ne'
    have h1 : d.D₁ w ≠ 0 := by
      rw [hD₁w w, hwv]
      exact mul_ne_zero he hv'
    have h2 : d.D₂ w = 0 := (d.disjoint w).resolve_left h1
    rw [d.ord_f₂, h2, mul_zero]
  rw [WeilDatum.pairing, WeilDatum.pairing, hnum, hden]

end Ws23WeilAdj

open AlgebraicCurve in
theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u) (hsep : SeparableAlong K u)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {n : ℕ} (d : WeilDatum K F' n) (d₀ : WeilDatum K F n)
    (hD₁ : d.D₁ = Divisor.pullbackAlong u hu d₀.D₁) (hf₁ : d.f₁ = u d₀.f₁)
    (hD₂ : d₀.D₂ = Divisor.pushforwardAlong u hu d.D₂)
    (hf₂ : d₀.f₂ = (letI := algebraAlong u; Algebra.norm F d.f₂)) :
    d.pairing = d₀.pairing :=
  Ws23WeilAdj.main u hu hfin hsep hratF hratF' d d₀ hD₁ hf₁ hD₂ hf₂

end S_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
end P2MW
export P2MW.S_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong (solution)
