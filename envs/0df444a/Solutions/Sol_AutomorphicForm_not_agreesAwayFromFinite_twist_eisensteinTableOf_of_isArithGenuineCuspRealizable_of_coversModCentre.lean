-- Prove2me | solution 1 for AutomorphicForm.not_agreesAwayFromFinite_twist_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/19c52cf2-39e1-588c-bc2a-cfb8f0c8327f

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
import Theorems.Thm_AutomorphicForm_exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_not_agreesAwayFromFinite_twist_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace Ws23
namespace GEIS

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal Polynomial
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem twistFactor_eq (v : HeightOneSpectrum (𝓞 F)) :
    ((((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  ring_nf

theorem eulerFactor_twist_eq (Θ Ψ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F))
    (hab : Ψ.a v = Θ.a v ∧ Ψ.b v = Θ.b v) (z : ℂ) (P : Prop) [Decidable P] (s : ℂ) :
    (if P then C 1 - C (z * (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).a v) * X
          + C (z ^ 2 * (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) =
    (if P then C 1 - C (z * Ψ.a v) * X + C (z ^ 2 * Ψ.b v) * X ^ 2 else C 1 : ℂ[X]).eval
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))) := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have hsplit : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2)) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ)) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) := by
    rw [neg_add, Complex.cpow_add _ _ hN, mul_comm]
  split_ifs
  · simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow, HeckeEigensystem.twist_a,
      HeckeEigensystem.twist_b, twistFactor_eq, hab.1, hab.2, hsplit]
    ring
  · simp only [eval_C]

theorem main (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ∃ Ψ : HeckeEigensystem F ℂ, Ψ.AgreesAwayFromFinite Θ ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Ψ) :
    ∀ (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (μ₁ μ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 F) F μ₁ → IsIdeleClassChar (𝓞 F) F μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite
          (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (eisensteinTableOf F N hN μ₁ μ₂) := by
  intro N hN μ₁ μ₂ h₁ h₂ hc₁ hc₂
  obtain ⟨Ψ, ⟨S₁, hS₁⟩, hΨ⟩ := hΘ
  refine LanglandsTunnell.Converse.not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist F _
    (fun χ hχ hχc _ => ?_) N hN μ₁ μ₂ h₁ h₂ hc₁ hc₂
  obtain ⟨S, hS₁S, σ₀, Λ, hΛ, hprod⟩ :=
    AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable F c u d₁ d₂ T hd hcov Ψ hΨ
      χ hχ hχc S₁
  refine ⟨S, σ₀ - 1 / 2, fun s => Λ (s + 1 / 2), hΛ.comp (differentiable_id.add_const _), fun s hs => ?_⟩
  have hs' : σ₀ < (s + 1 / 2).re := by
    simp only [Complex.add_re, Complex.div_re, Complex.one_re, Complex.re_ofNat, Complex.one_im, Complex.im_ofNat]
    norm_num
    linarith
  have hp := hprod (s + 1 / 2) hs'
  have hfun : (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((if IsUnramifiedCharAt χ v.1
        then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) *
            (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).a v.1) * X
          + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) *
            (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v.1) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) =
      fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((if IsUnramifiedCharAt χ v.1
        then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * Ψ.a v.1) * X
          + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * Ψ.b v.1) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹ := by
    funext v
    have hv : v.1 ∉ S₁ := fun h => v.2 (hS₁S h)
    rw [Units.val_pow_eq_pow_val]
    rw [eulerFactor_twist_eq Θ Ψ v.1 (hS₁ v.1 hv) _ _ s]
  rw [hfun]
  exact hp

end Ws23.GEIS

end

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ∃ Ψ : HeckeEigensystem F ℂ, Ψ.AgreesAwayFromFinite Θ ∧
      IsArithGenuineCuspRealizable F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Ψ) :
    ∀ (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (μ₁ μ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 F) F μ₁ → IsIdeleClassChar (𝓞 F) F μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite
          (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (eisensteinTableOf F N hN μ₁ μ₂) :=
  Ws23.GEIS.main F c u d₁ d₂ T hd hcov Θ hΘ

end S_AutomorphicForm_not_agreesAwayFromFinite_twist_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_not_agreesAwayFromFinite_twist_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre (solution)
