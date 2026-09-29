-- Prove2me | solution 1 for AlgebraicCurve.Pic0.roof_package_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7afc91f0-aa88-541e-a3e2-9585a97b090c

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_ShimuraKernel
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_roof_package_of_surjective
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"

set_option autoImplicit false

open AlgebraicCurve

namespace ROOFID

variable {K F₁ F₂ : Type} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]

theorem finiteAlong_and_finrankAlong_eq_one (ι : F₁ →ₐ[K] F₂) (hιs : Function.Surjective ι) :
    FiniteAlong K ι ∧ finrankAlong K ι = 1 := by
  letI : Algebra F₁ F₂ := algebraAlong ι

  let e : F₁ ≃ₗ[F₁] F₂ :=
    LinearEquiv.ofBijective
      { toFun := ι, map_add' := map_add ι, map_smul' := fun a b => by
          show ι (a * b) = ι a * ι b
          exact map_mul ι a b }
      ⟨ι.toRingHom.injective, hιs⟩
  refine ⟨?_, ?_⟩
  · exact Module.Finite.equiv e
  · show Module.finrank F₁ F₂ = 1
    rw [← e.finrank_eq, Module.finrank_self]

end ROOFID

theorem solution
    {K F₀ F₁ F₂ : Type} [Field K] [CharZero K] [Field F₀] [Field F₁] [Field F₂]
    [Algebra K F₀] [Algebra K F₁] [Algebra K F₂]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
    (ι : F₁ →ₐ[K] F₂) (hι : ι.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K ι hι)
    (hιs : Function.Surjective ι)
    (α : F₀ →ₐ[K] F₁) (hα : α.toRingHom.IsIntegral) (hια : (ι.comp α).toRingHom.IsIntegral)
    (W : F₁ ≃ₐ[K] F₁) :
    (∀ D : Divisor K F₁, Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι D) = D) ∧
    Function.Surjective (Pic0.pullbackAlongHom ι hι hFI) ∧
    (∀ D : Divisor K F₁,
      Divisor.pushforwardAlong (ι.comp α) hια (Divisor.pullbackAlong ι hι D) = Divisor.pushforwardAlong α hα D) ∧
    ∃ θ : F₂ ≃ₐ[K] F₂, (∀ a : F₁, θ (ι a) = ι (W.symm a)) ∧
      ∀ x₁ : Pic0 K F₁,
        SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFI x₁ =
          Pic0.pullbackAlongHom ι hι hFI (SemilinearAut.ofAlgAut W.symm • x₁) := by
  classical

  have hdeg : ∀ D : Divisor K F₁, Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι D) = D :=
    fun D => Divisor.pushforwardAlong_pullbackAlong_of_surjective ι hι hιs D

  obtain ⟨hfin, hrk⟩ := ROOFID.finiteAlong_and_finrankAlong_eq_one (K := K) ι hιs
  have hpp : ∀ E : Divisor K F₂, Divisor.pullbackAlong ι hι (Divisor.pushforwardAlong ι hι E) = E := by
    intro E
    have h := Divisor.pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
      ι hι hfin 1 hrk (fun _ => AlgEquiv.refl) (fun _ => by ext x; rfl) (fun a b _ => Subsingleton.elim a b) E
    rw [h, Fin.sum_univ_one]
    show SemilinearAut.ofAlgAut (1 : F₂ ≃ₐ[K] F₂) • E = E
    rw [map_one, one_smul]
  refine ⟨hdeg, ?_, ?_, ?_⟩

  · intro y
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    refine ⟨Pic0.mk (Pic0.pushforwardAlongDegZero ι hι E), ?_⟩
    rw [Pic0.pullbackAlongHom_mk]
    congr 1
    apply Subtype.ext
    rw [Pic0.coe_pullbackAlongDegZeroHom, Pic0.coe_pushforwardAlongDegZero, hpp]

  · intro D
    rw [Divisor.pushforwardAlong_comp α ι hα hι hια, hdeg]

  · let ιe : F₁ ≃ₐ[K] F₂ := AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hιs⟩
    have hιe : ∀ a, ιe a = ι a := fun _ => rfl
    refine ⟨(ιe.symm.trans W.symm).trans ιe, ?_, ?_⟩
    · intro a
      show ιe (W.symm (ιe.symm (ι a))) = ι (W.symm a)
      rw [← hιe a, AlgEquiv.symm_apply_apply, hιe]
    · have hint : SemilinearAut.IntertwinesAlong ι.toRingHom (SemilinearAut.ofAlgAut W.symm)
          (SemilinearAut.ofAlgAut ((ιe.symm.trans W.symm).trans ιe)) := by
        intro x
        rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
        show ιe (W.symm (ιe.symm (ι x))) = ι (W.symm x)
        rw [← hιe x, AlgEquiv.symm_apply_apply, hιe]
      intro x₁
      obtain ⟨D, rfl⟩ := Pic0.mk_surjective x₁
      rw [Pic0.pullbackAlongHom_mk, SemilinearAut.pic0_smul_mk, SemilinearAut.pic0_smul_mk, Pic0.pullbackAlongHom_mk]
      congr 1
      apply Subtype.ext
      rw [SemilinearAut.coe_degZeroSMulHom, Pic0.coe_pullbackAlongDegZeroHom, Pic0.coe_pullbackAlongDegZeroHom,
        SemilinearAut.coe_degZeroSMulHom, SemilinearAut.pullbackAlong_smul ι hι hint]

end S_AlgebraicCurve_Pic0_roof_package_of_surjective
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_roof_package_of_surjective (solution)
