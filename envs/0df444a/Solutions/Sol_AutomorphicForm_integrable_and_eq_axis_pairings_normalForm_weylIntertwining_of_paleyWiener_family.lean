-- Prove2me | solution 1 for AutomorphicForm.integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/71751137-81cd-5790-b455-067fad286fb2

import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open scoped ComplexConjugate
open Filter

namespace Ws31
namespace AX

theorem eventuallyEq_nhdsNE_of_analyticOnNhd_of_meromorphicOn
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : MeromorphicOn G Set.univ)
    (h : ∀ s ∈ V, F s = G s) :
    ∀ s ∈ U, F =ᶠ[𝓝[≠] s] G := by
  let W : Set ℂ := {z | F =ᶠ[𝓝[≠] z] G}
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hz' : ∀ᶠ w in 𝓝 z, w ≠ z → F w = G w := eventually_nhdsWithin_iff.mp hz
    obtain ⟨O, hO, hOo, hzO⟩ := eventually_nhds_iff.mp hz'
    refine Filter.mem_of_superset (hOo.mem_nhds hzO) fun w hw => ?_
    show F =ᶠ[𝓝[≠] w] G
    by_cases hwz : w = z
    · subst hwz; exact hz
    · have hmem : O ∩ {z}ᶜ ∈ 𝓝 w := (hOo.inter isOpen_compl_singleton).mem_nhds ⟨hw, hwz⟩
      have hall : ∀ᶠ y in 𝓝 w, F y = G y :=
        Filter.mem_of_superset hmem fun y hy => hO y hy.1 hy.2
      exact hall.filter_mono nhdsWithin_le_nhds
  have hVW : V ⊆ W := fun z hz =>
    show F =ᶠ[𝓝[≠] z] G from
      nhdsWithin_le_nhds (Filter.eventually_of_mem (hV.mem_nhds hz) fun y hy => h y hy)
  have hcl : closure W ∩ U ⊆ W := by
    rintro z ⟨hzc, hzU⟩
    have hFm : MeromorphicAt F z := (hF z hzU).meromorphicAt
    have hGm : MeromorphicAt G z := hG z (Set.mem_univ z)
    have hHm : MeromorphicAt (F - G) z := hFm.sub hGm
    have hfreq : ∃ᶠ y in 𝓝[≠] z, (F - G) y = 0 := by
      rw [Filter.Frequently]
      intro hne
      have hne' : ∀ᶠ y in 𝓝 z, y ≠ z → ¬(F - G) y = 0 := eventually_nhdsWithin_iff.mp hne
      obtain ⟨O, hO, hOo, hzO⟩ := eventually_nhds_iff.mp hne'
      obtain ⟨w, hwO, hwW⟩ := mem_closure_iff.mp hzc O hOo hzO
      have hwev : ∀ᶠ y in 𝓝[≠] w, F y = G y := hwW
      have hOw : ∀ᶠ y in 𝓝[≠] w, y ∈ O ∧ y ≠ z := by
        have h1 : ∀ᶠ y in 𝓝[≠] w, y ∈ O := nhdsWithin_le_nhds (hOo.mem_nhds hwO)
        by_cases hwz : w = z
        · subst hwz
          exact h1.and (eventually_nhdsWithin_of_forall fun y hy => hy)
        · have h2 : ∀ᶠ y in 𝓝[≠] w, y ≠ z :=
            nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hwz)
          exact h1.and h2
      obtain ⟨y, hyFG, hyO, hyz⟩ := (hwev.and hOw).exists
      exact hO y hyO hyz (by simp [hyFG])
    have hzero : ∀ᶠ y in 𝓝[≠] z, (F - G) y = 0 :=
      (hHm.frequently_zero_iff_eventuallyEq_zero).mp hfreq
    show F =ᶠ[𝓝[≠] z] G
    exact hzero.mono fun y hy => by simpa [sub_eq_zero] using hy
  have hsub : U ⊆ W := hUc.subset_of_closure_inter_subset hWo (by
    obtain ⟨v, hv⟩ := hVne; exact ⟨v, hVU hv, hVW hv⟩) hcl
  exact fun s hs => hsub hs

end Ws31.AX

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
      (r : ι → ι) (_hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
      (_hdist : ∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite F (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth F (ψf e s))
      (_hψKu : ∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (N : Ideal (𝓞 F)) (_hN : N ≠ ⊥)
      (_hψlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ψf e s (g * u) = ψf e s g)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (Mc : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ (e : ι) (g : AdelicGL2 (𝓞 F) F), MeromorphicNFOn (fun s : ℂ => Mc e s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc e s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s) g)
      (e : ι),
    let a : ι → ℝ → adelicMaximalCompact F → ℂ :=
      fun e t k => ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
    let b : ι → ℝ → adelicMaximalCompact F → ℂ :=
      fun e t k => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
        Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F))
    let A : ι → ℝ → ℂ := fun e t => ∫ k, a e t k * conj (a e t k) ∂(maximalCompactHaar F)
    let B : ι → ℝ → ℂ := fun e t => ∫ k, a e t k * conj (b e t k) ∂(maximalCompactHaar F)
    let C : ι → ℝ → ℂ := fun e t => ∫ k, b e t k * conj (b e t k) ∂(maximalCompactHaar F)
    Integrable (A e) ∧ Integrable (B e) ∧ Integrable (C e) ∧
    (∀ t : ℝ, Integrable (fun k => a e t k * conj (b e t k)) (maximalCompactHaar F)) ∧
    (∀ t : ℝ, Integrable (fun k => b e t k * conj (b e t k)) (maximalCompactHaar F)) ∧
    (∀ t : ℝ, C e t = A (r e) (-t)) := by
  intro α hα ι _ μ ν _hμ _hν _hμic _hνic _hμc r _hr _hdist ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu N _hN _hψlev
    _hνc _hψdec Mc _hMc e
  intro a b A B C
  classical

  have hdata : ∀ j : ι, ∃ (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = ψf j s g + ∑' ξ : F, ψf j s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf j s) g) := fun j =>
    AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
      F hα (μ j) (ν j) (_hμ j) (_hν j) (_hμic j) (_hνic j) (_hμc j) (_hνc j) (ψf j) (_hψf j) (_hψK j) (_hψsm j)
      (_hψjc j) (_hψhol j) (_hψKu j)
  obtain ⟨O, Ec, Nc, hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEeq, hNeq⟩ := hdata (r e)

  have hId : ∀ (s₀ : ℂ), s₀ ∈ O → ∀ g : AdelicGL2 (𝓞 F) F,
      limUnder (𝓝[≠] s₀) (fun s : ℂ => Mc (r e) s g) = Nc s₀ g := by
    intro s₀ hs₀ g
    have hgerm := Ws31.AX.eventuallyEq_nhdsNE_of_analyticOnNhd_of_meromorphicOn hO hOc
      (V := {s : ℂ | 1 / 2 < s.re}) (isOpen_lt continuous_const Complex.continuous_re) hhalf
      ⟨1, by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num⟩ (hNan g) (_hMc (r e) g).1.meromorphicOn
      (fun s hs => by rw [hNeq s hs g, (_hMc (r e) g).2 s hs]) s₀ hs₀
    have hcont : ContinuousAt (fun s => Nc s g) s₀ := (hNan g s₀ hs₀).continuousAt
    refine Filter.Tendsto.limUnder_eq ?_
    exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hgerm
  have haxis : ∀ t : ℝ, (-((t : ℂ) * Complex.I)) ∈ O := fun t => hax (by simp)
  have hb : ∀ t k, b e t k = ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nc (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F) := by
    intro t k
    show ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * limUnder (𝓝[≠] (-((t : ℂ) * Complex.I))) (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F)) = _
    rw [hId _ (haxis t)]

  have hU : ∀ t : ℝ, C e t = A (r e) (-t) := by
    intro t
    have h := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
      F hα (μ (r e)) (ν (r e)) (_hμ _) (_hν _) (_hμic _) (_hνic _) (_hμc _) (_hνc _)
      (ψf (r e)) (_hψf _) (_hψK _) (_hψsm _) (_hψjc _) (_hψhol _) (_hψKu _)
      (ψf (r e)) (_hψf _) (_hψK _) (_hψsm _) (_hψjc _) (_hψhol _) (_hψKu _)
      O Ec Nc ⟨hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEeq, hNeq⟩
      O Ec Nc ⟨hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEeq, hNeq⟩ (-t)
    have ecast : (((-t : ℝ) : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by push_cast; ring
    rw [ecast] at h
    show (∫ k, b e t k * conj (b e t k) ∂(maximalCompactHaar F)) = ∫ k, a (r e) (-t) k * conj (a (r e) (-t) k) ∂(maximalCompactHaar F)
    have lhs : (fun k : adelicMaximalCompact F => b e t k * conj (b e t k)) = fun k : adelicMaximalCompact F =>
        (((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nc (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F)) *
        conj (((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nc (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F)) := by
      funext k; rw [hb]
    have rhs : (fun k : adelicMaximalCompact F => a (r e) (-t) k * conj (a (r e) (-t) k)) = fun k : adelicMaximalCompact F =>
        ψf (r e) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F) * conj (ψf (r e) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F)) := by
      funext k
      show ψf (r e) (((-t : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf (r e) (((-t : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) = _
      rw [ecast]
    rw [lhs, rhs]
    beta_reduce at h
    exact h

  have hCK : IsCompact ((adelicMaximalCompact F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) :=
    AutomorphicForm.isCompact_adelicMaximalCompact F
  have hdec : ∀ j : ι, ∃ m : ℝ → ℝ, Integrable m ∧ (∃ Bm : ℝ, ∀ t, m t ≤ Bm) ∧
      ∀ (t : ℝ) (k : adelicMaximalCompact F), ‖a j t k‖ ≤ m t := by
    intro j
    obtain ⟨m, hm, hB, hmt⟩ := _hψdec j 0 0 _ hCK
    refine ⟨m, hm, hB, fun t k => ?_⟩
    have := hmt 0 (by simp) t (k : AdelicGL2 (𝓞 F) F) k.2
    simpa [a] using this

  have ha_c : ∀ j : ι, Continuous (fun p : ℝ × adelicMaximalCompact F => a j p.1 p.2) := by
    intro j
    show Continuous (fun p : ℝ × adelicMaximalCompact F => ψf j ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 F) F))
    exact (_hψjc j).comp (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd))
  have hN_c : Continuous (fun p : ℝ × adelicMaximalCompact F => Nc (-((p.1 : ℂ) * Complex.I)) (p.2 : AdelicGL2 (𝓞 F) F)) := by
    have hg : Continuous (fun p : ℝ × adelicMaximalCompact F => ((-((p.1 : ℂ) * Complex.I)), (p.2 : AdelicGL2 (𝓞 F) F))) :=
      (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).neg).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hNc.comp_continuous hg fun p => ⟨haxis p.1, Set.mem_univ _⟩
  have hb_c : Continuous (fun p : ℝ × adelicMaximalCompact F => b e p.1 p.2) := by
    have e1 : (fun p : ℝ × adelicMaximalCompact F => b e p.1 p.2) = fun p =>
        ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nc (-((p.1 : ℂ) * Complex.I)) (p.2 : AdelicGL2 (𝓞 F) F) := by
      funext p; rw [hb]
    rw [e1]
    exact continuous_const.mul hN_c

  have intK : ∀ f : adelicMaximalCompact F → ℂ, Continuous f → Integrable f (maximalCompactHaar F) := fun f hf =>
    integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
  have intKr : ∀ f : adelicMaximalCompact F → ℝ, Continuous f → Integrable f (maximalCompactHaar F) := fun f hf =>
    integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
  have hak : ∀ j t, Continuous (fun k : adelicMaximalCompact F => a j t k) := fun j t =>
    (ha_c j).comp (continuous_const.prodMk continuous_id)
  have hbk : ∀ t, Continuous (fun k : adelicMaximalCompact F => b e t k) := by
    intro t
    have e1 : (fun k : adelicMaximalCompact F => b e t k) = fun k : adelicMaximalCompact F =>
        ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nc (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F) :=
      funext fun k => hb t k
    rw [e1]
    exact continuous_const.mul ((hNc.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      fun k => ⟨haxis t, Set.mem_univ _⟩))
  have hconjb : ∀ t, Continuous (fun k : adelicMaximalCompact F => conj (b e t k)) := fun t =>
    Complex.continuous_conj.comp (hbk t)
  have habk : ∀ t, Integrable (fun k => a e t k * conj (b e t k)) (maximalCompactHaar F) := fun t =>
    intK (fun k => a e t k * conj (b e t k)) ((hak e t).mul (hconjb t))
  have hbbk : ∀ t, Integrable (fun k => b e t k * conj (b e t k)) (maximalCompactHaar F) := fun t =>
    intK (fun k => b e t k * conj (b e t k)) ((hbk t).mul (hconjb t))

  set Ar : ι → ℝ → ℝ := fun j t => ∫ k, ‖a j t k‖ ^ 2 ∂(maximalCompactHaar F) with hAr
  set Cr : ℝ → ℝ := fun t => ∫ k, ‖b e t k‖ ^ 2 ∂(maximalCompactHaar F) with hCr
  have hmc : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hA_eq : ∀ j t, A j t = ((Ar j t : ℝ) : ℂ) := by
    intro j t
    show (∫ k, a j t k * conj (a j t k) ∂(maximalCompactHaar F)) = ((∫ k, ‖a j t k‖ ^ 2 ∂(maximalCompactHaar F) : ℝ) : ℂ)
    rw [← integral_complex_ofReal]
    congr 1; funext k; exact hmc _
  have hC_eq : ∀ t, C e t = ((Cr t : ℝ) : ℂ) := by
    intro t
    show (∫ k, b e t k * conj (b e t k) ∂(maximalCompactHaar F)) = ((∫ k, ‖b e t k‖ ^ 2 ∂(maximalCompactHaar F) : ℝ) : ℂ)
    rw [← integral_complex_ofReal]
    congr 1; funext k; exact hmc _
  have hCr_eq : ∀ t, Cr t = Ar (r e) (-t) := by
    intro t
    have := hU t
    rw [hC_eq, hA_eq] at this
    exact_mod_cast this

  have hAr_c : ∀ j, Continuous (Ar j) := by
    intro j
    have hF : Continuous (fun p : ℝ × adelicMaximalCompact F => ‖a j p.1 p.2‖ ^ 2) := (ha_c j).norm.pow 2
    have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar F)
      (f := fun (t : ℝ) (k : adelicMaximalCompact F) => ‖a j t k‖ ^ 2) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hB_c : Continuous (B e) := by
    have hF : Continuous (fun p : ℝ × adelicMaximalCompact F => a e p.1 p.2 * conj (b e p.1 p.2)) :=
      (ha_c e).mul (Complex.continuous_conj.comp hb_c)
    have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar F)
      (f := fun (t : ℝ) (k : adelicMaximalCompact F) => a e t k * conj (b e t k)) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this

  have hAr_int : ∀ j, Integrable (Ar j) := by
    intro j
    obtain ⟨m, hm, ⟨Bm, hBm⟩, hmt⟩ := hdec j
    have hm0 : ∀ t, 0 ≤ m t := fun t => (norm_nonneg _).trans (hmt t ⟨1, one_mem _⟩)
    refine Integrable.mono' (hm.const_mul Bm) (hAr_c j).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun k => by positivity)]
    calc (∫ k, ‖a j t k‖ ^ 2 ∂(maximalCompactHaar F)) ≤ ∫ k, m t ^ 2 ∂(maximalCompactHaar F) := by
          refine integral_mono (intKr _ (((hak j t).norm).pow 2)) (integrable_const _) fun k => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (hmt t k) 2
      _ = m t ^ 2 := by simp
      _ ≤ Bm * m t := by rw [sq]; exact mul_le_mul_of_nonneg_right (hBm t) (hm0 t)
  have hAint : ∀ j, Integrable (A j) := by
    intro j
    have e1 : A j = fun t => ((Ar j t : ℝ) : ℂ) := funext (hA_eq j)
    rw [e1]
    exact (hAr_int j).ofReal
  have hCr_int : Integrable Cr := by
    have e1 : Cr = fun t => Ar (r e) (-t) := funext hCr_eq
    rw [e1]
    exact (hAr_int (r e)).comp_neg
  have hCint : Integrable (C e) := by
    have e1 : C e = fun t => ((Cr t : ℝ) : ℂ) := funext hC_eq
    rw [e1]
    exact hCr_int.ofReal
  have hBint : Integrable (B e) := by
    refine Integrable.mono' ((hAr_int e).add hCr_int |>.div_const 2) hB_c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    show ‖∫ k, a e t k * conj (b e t k) ∂(maximalCompactHaar F)‖ ≤ (Ar e t + Cr t) / 2
    calc ‖∫ k, a e t k * conj (b e t k) ∂(maximalCompactHaar F)‖
        ≤ ∫ k, ‖a e t k * conj (b e t k)‖ ∂(maximalCompactHaar F) := norm_integral_le_integral_norm _
      _ ≤ ∫ k, (‖a e t k‖ ^ 2 + ‖b e t k‖ ^ 2) / 2 ∂(maximalCompactHaar F) := by
          refine integral_mono (habk t).norm (intKr _ ((((hak e t).norm.pow 2).add ((hbk t).norm.pow 2)).div_const 2)) fun k => ?_
          show ‖a e t k * conj (b e t k)‖ ≤ (‖a e t k‖ ^ 2 + ‖b e t k‖ ^ 2) / 2
          rw [norm_mul, Complex.norm_conj]
          nlinarith [sq_nonneg (‖a e t k‖ - ‖b e t k‖)]
      _ = (Ar e t + Cr t) / 2 := by
          simp only [hAr, hCr]
          rw [integral_div, integral_add (intKr _ ((hak e t).norm.fun_pow 2)) (intKr _ ((hbk t).norm.fun_pow 2))]
  exact ⟨hAint e, hBint, hCint, habk, hbbk, hU⟩

end S_AutomorphicForm_integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family
end P2MW
export P2MW.S_AutomorphicForm_integrable_and_eq_axis_pairings_normalForm_weylIntertwining_of_paleyWiener_family (solution)
