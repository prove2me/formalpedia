-- Prove2me | solution 1 for AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8dfd7c74-14d4-578d-a656-ee2855975fc5

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply"
p2m_attr_erase "simp" "IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul"
p2m_attr_erase "simp" "FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal

noncomputable section

namespace R1S78Axis

def spine (t : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 0} ∪ ({s : ℂ | s.im = t} ∩ {s : ℂ | 0 ≤ s.re} ∩ {s : ℂ | s.re ≤ 1}) ∪
    {s : ℂ | 1 / 2 < s.re}

theorem isPreconnected_spine (t : ℝ) : IsPreconnected (spine t) := by
  have hL : IsPreconnected {s : ℂ | s.re = 0} :=
    (convex_hyperplane (IsLinearMap.mk Complex.add_re Complex.smul_re) (0 : ℝ)).isPreconnected
  have hSeg : IsPreconnected ({s : ℂ | s.im = t} ∩ {s : ℂ | 0 ≤ s.re} ∩ {s : ℂ | s.re ≤ 1}) :=
    (((convex_hyperplane (IsLinearMap.mk Complex.add_im Complex.smul_im) t).inter
      (convex_halfSpace_re_ge 0)).inter (convex_halfSpace_re_le 1)).isPreconnected
  have hH : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2)).isPreconnected

  have h1 : IsPreconnected ({s : ℂ | s.re = 0} ∪
      ({s : ℂ | s.im = t} ∩ {s : ℂ | 0 ≤ s.re} ∩ {s : ℂ | s.re ≤ 1})) := by
    refine IsPreconnected.union ((t : ℂ) * Complex.I) ?_ ?_ hL hSeg
    · simp
    · simp

  refine IsPreconnected.union (1 + (t : ℂ) * Complex.I) ?_ ?_ h1 hH
  · refine Or.inr ?_
    simp
  · show 1 / 2 < (1 + (t : ℂ) * Complex.I).re
    simp; norm_num

theorem zero_mem_spine (t : ℝ) : (0 : ℂ) ∈ spine t :=
  Or.inl (Or.inl (by simp))

theorem spine_subset (c : ℂ) (hc : c.re = 1 / 2) :
    spine (c.im + 1) ⊆ {s : ℂ | 0 ≤ s.re} \ {c} := by
  intro s hs
  rcases hs with (hs | ⟨⟨hsim, hs0⟩, _⟩) | hs
  · refine ⟨?_, ?_⟩
    · show 0 ≤ s.re
      rw [Set.mem_setOf_eq] at hs
      rw [hs]
    · rintro (rfl : s = c)
      rw [Set.mem_setOf_eq] at hs
      rw [hs] at hc
      norm_num at hc
  · refine ⟨hs0, ?_⟩
    rintro (rfl : s = c)
    rw [Set.mem_setOf_eq] at hsim
    linarith
  · refine ⟨?_, ?_⟩
    · show 0 ≤ s.re
      rw [Set.mem_setOf_eq] at hs
      linarith
    · rintro (rfl : s = c)
      rw [Set.mem_setOf_eq] at hs
      rw [hc] at hs
      norm_num at hs

theorem exists_isOpen_isPreconnected (G : Set ℂ) (hG : IsOpen G) (c : ℂ) (hc : c.re = 1 / 2)
    (hsub : {s : ℂ | 0 ≤ s.re} \ {c} ⊆ G) :
    ∃ O : Set ℂ, IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧
      {s : ℂ | 1 / 2 < s.re} ⊆ O ∧ O ⊆ G := by
  set P : Set ℂ := spine (c.im + 1) with hP
  have hPG : P ⊆ G := (spine_subset c hc).trans hsub
  have hballs : ∀ p ∈ P, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ G := fun p hp =>
    Metric.isOpen_iff.mp hG p (hPG hp)
  choose! ε hε hεG using hballs
  refine ⟨⋃ p ∈ P, Metric.ball p (ε p), isOpen_biUnion fun _ _ => Metric.isOpen_ball, ?_, ?_, ?_, ?_⟩
  ·
    have hPO : P ⊆ ⋃ p ∈ P, Metric.ball p (ε p) := fun p hp =>
      Set.mem_biUnion hp (Metric.mem_ball_self (hε p hp))
    have hne : P.Nonempty := ⟨0, zero_mem_spine _⟩
    have key : (⋃ p ∈ P, Metric.ball p (ε p)) = ⋃ p : P, (P ∪ Metric.ball (p : ℂ) (ε p)) := by
      apply Set.Subset.antisymm
      · intro s hs
        obtain ⟨p, hp, hsp⟩ := Set.mem_iUnion₂.mp hs
        exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Or.inr hsp⟩
      · intro s hs
        obtain ⟨p, hsp⟩ := Set.mem_iUnion.mp hs
        rcases hsp with hsp | hsp
        · exact hPO hsp
        · exact Set.mem_biUnion p.2 hsp
    rw [key]
    haveI : Nonempty P := hne.to_subtype
    refine isPreconnected_iUnion ⟨0, Set.mem_iInter.mpr fun p => Or.inl (zero_mem_spine _)⟩ ?_
    intro p
    exact IsPreconnected.union (p : ℂ) p.2 (Metric.mem_ball_self (hε p p.2))
      (isPreconnected_spine _) (convex_ball (p : ℂ) (ε p)).isPreconnected
  · intro s hs
    have hsP : s ∈ P := Or.inl (Or.inl hs)
    exact Set.mem_biUnion hsP (Metric.mem_ball_self (hε s hsP))
  · intro s hs
    have hsP : s ∈ P := Or.inr hs
    exact Set.mem_biUnion hsP (Metric.mem_ball_self (hε s hsP))
  · intro s hs
    obtain ⟨p, hp, hsp⟩ := Set.mem_iUnion₂.mp hs
    exact hεG p hp hsp

end R1S78Axis

end

open R1S78Axis in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W),
    letI := adeleBorel (𝓞 F) F
    ∃ (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) := by
  intro α hα μ ν hμ hν hμic hνic hμk hνk φ hφ hφK hφf hφjc hφhol hφKu
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F

  have hcont : ∀ s, Continuous (φ s) := fun s => hφjc.comp (Continuous.prodMk_right s)

  obtain ⟨U₁, V, hU₁, hU₁sub, hVa, hVc, hVeq⟩ :=
    AutomorphicForm.exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
      F hα μ ν hμ hν hμic hνic hμk hνk φ hφ hφK hφf hφjc hφhol hφKu

  obtain ⟨c, U₂, Nc, hc, hU₂, hU₂sub, hNa, hNc, hNeq⟩ :=
    AutomorphicForm.exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
      F hα μ ν hμ hν hμic hνic hμk hνk φ hφ hφK hφf hφjc hφhol hφKu

  have hGsub : {s : ℂ | 0 ≤ s.re} \ {c} ⊆ U₁ ∩ U₂ := fun s hs => ⟨hU₁sub hs.1, hU₂sub hs⟩
  obtain ⟨O, hO, hOc, hax, hhp, hOG⟩ :=
    exists_isOpen_isPreconnected (U₁ ∩ U₂) (hU₁.inter hU₂) c hc hGsub
  have hO₁ : O ⊆ U₁ := fun s hs => (hOG hs).1
  have hO₂ : O ⊆ U₂ := fun s hs => (hOG hs).2

  set cvol : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ with hcvol

  refine ⟨O, fun s g => φ s g + cvol * Nc s g + V s g, Nc, hO, hOc, hax, hhp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g
    have h1 : AnalyticOnNhd ℂ (fun s => φ s g) O :=
      (hφhol g).differentiableOn.analyticOnNhd hO
    have h2 : AnalyticOnNhd ℂ (fun s => cvol * Nc s g) O :=
      analyticOnNhd_const.mul ((hNa g).mono hO₂)
    have h3 : AnalyticOnNhd ℂ (fun s => V s g) O := (hVa g).mono hO₁
    exact (h1.add h2).add h3
  ·
    intro g
    exact (hNa g).mono hO₂
  ·
    have h1 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2) (O ×ˢ Set.univ) :=
      hφjc.continuousOn
    have h2 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => cvol * Nc p.1 p.2) (O ×ˢ Set.univ) :=
      continuousOn_const.mul (hNc.mono (Set.prod_mono hO₂ subset_rfl))
    have h3 : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => V p.1 p.2) (O ×ˢ Set.univ) :=
      hVc.mono (Set.prod_mono hO₁ subset_rfl)
    exact (h1.add h2).add h3
  ·
    exact hNc.mono (Set.prod_mono hO₂ subset_rfl)
  ·
    intro s hs g
    have hct :
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => unipotentGL2 t)
            (fun g' : AdelicGL2 (𝓞 F) F => φ s g' + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')) g
          = φ s g + cvol * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g :=
      AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
        F hα μ ν hμ hν s hs (φ s) (hφ s) (hcont s) g
    have hV := hVeq s g hs
    beta_reduce at hV
    rw [hct] at hV
    show φ s g + cvol * Nc s g + V s g = _
    rw [hV, hNeq s hs g]
    ring
  ·
    exact hNeq

end S_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family (solution)
