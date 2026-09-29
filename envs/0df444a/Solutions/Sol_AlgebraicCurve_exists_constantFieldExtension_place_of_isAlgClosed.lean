-- Prove2me | solution 1 for AlgebraicCurve.exists_constantFieldExtension_place_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a2fa40f8-8e6e-51c7-89f2-3c9b05700d93

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_constantFieldExtension_place_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open AlgebraicCurve

namespace ConstExtC

theorem subfield_closure_eq_top {K' F₀ F' : Type*} [Field K'] [Field F₀] [Field F']
    [Algebra K' F'] (f : F₀ →+* F')
    (hgen : IntermediateField.adjoin K' (Set.range f) = ⊤) :
    Subfield.closure (Set.range (algebraMap K' F') ∪ Set.range f) = ⊤ := by
  have h := congrArg IntermediateField.toSubfield hgen
  rw [IntermediateField.adjoin_toSubfield] at h
  rw [h]
  rfl

end ConstExtC

theorem solution
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (emb : AlgebraicClosure ℚ →+* ℂ) :
    ∃ (Fc : Type) (_ : Field Fc) (_ : Algebra ℂ Fc) (_ : AlgebraicCurve.IsCurveOver ℂ Fc)
      (_ : Algebra.EssFiniteType ℂ Fc) (toC : Fbar →+* Fc)
      (bcPlace : Place (AlgebraicClosure ℚ) Fbar → Place ℂ Fc),
      (∀ z : AlgebraicClosure ℚ, toC (algebraMap (AlgebraicClosure ℚ) Fbar z) = algebraMap ℂ Fc (emb z)) ∧
      Subfield.closure (Set.range (algebraMap ℂ Fc) ∪ Set.range toC) = ⊤ ∧
      (∀ s : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : s => (x : Fbar)) →
        LinearIndependent ℂ (fun x : s => toC (x : Fbar))) ∧
      (∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : Fbar), toC x ∈ (bcPlace P).toValuationSubring ↔ x ∈ P.toValuationSubring) ∧
      Function.Injective bcPlace := by
  classical

  letI instAlgKC : Algebra (AlgebraicClosure ℚ) ℂ := emb.toAlgebra
  have halg : ∀ z : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ℂ z = emb z := fun _ => rfl

  obtain ⟨t, ht, hfd, -⟩ :=
    IsCurveOver.exists_separating_transcendental (K := AlgebraicClosure ℚ) (F := Fbar)
  have hfg₀ : ∃ x : Fbar, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set Fbar)) Fbar :=
    ⟨t, ht, hfd⟩

  haveI : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := Fbar) :=
    hasCanonicalDivisor_of_isCurveOver

  obtain ⟨Fc, instF, instAC, instAF, instAK, instT1, instT2, instCurve, instCan, hfg', hgen⟩ :=
    AlgebraicCurve.exists_constantFieldExtension (AlgebraicClosure ℚ) Fbar ℂ hfg₀

  have hess : Algebra.EssFiniteType ℂ Fc := by
    obtain ⟨x, hx, hxfd⟩ := hfg'
    exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hxfd

  have hP : ∀ P : Place (AlgebraicClosure ℚ) Fbar, ∃ P' : Place ℂ Fc,
      P'.toValuationSubring.comap (algebraMap Fbar Fc) = P.toValuationSubring ∧
      (∀ f : Fbar, P'.ord (algebraMap Fbar Fc f) = P.ord f) ∧
      ∀ Q' : Place ℂ Fc,
        Q'.toValuationSubring.comap (algebraMap Fbar Fc) = P.toValuationSubring → Q' = P' :=
    fun P => AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      (AlgebraicClosure ℚ) Fbar ℂ Fc hfg₀ hfg' hgen P
  choose bc hbc _hord _huniq using hP
  have hmem : ∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : Fbar),
      algebraMap Fbar Fc x ∈ (bc P).toValuationSubring ↔ x ∈ P.toValuationSubring := by
    intro P x
    rw [← ValuationSubring.mem_comap, hbc P]
  refine ⟨Fc, instF, instAC, instCurve, hess, algebraMap Fbar Fc, bc, ?_, ?_, ?_, hmem, ?_⟩
  ·
    intro z
    rw [← IsScalarTower.algebraMap_apply, ← halg z, ← IsScalarTower.algebraMap_apply]
  ·
    exact ConstExtC.subfield_closure_eq_top (algebraMap Fbar Fc) hgen
  ·
    intro s hs
    exact AlgebraicCurve.linearIndependent_of_constantFieldExtension (AlgebraicClosure ℚ) Fbar ℂ Fc
      hfg₀ hfg' hgen hs
  ·
    intro P Q hPQ
    apply Place.ext
    rw [← hbc P, ← hbc Q, hPQ]

end S_AlgebraicCurve_exists_constantFieldExtension_place_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_exists_constantFieldExtension_place_of_isAlgClosed (solution)
