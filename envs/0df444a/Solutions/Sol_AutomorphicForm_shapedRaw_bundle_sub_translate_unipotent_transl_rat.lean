-- Prove2me | solution 1 for AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/24476925-8986-5a4b-ac80-719cdf3ba367

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Theorems.Thm_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_WhittakerModel_localSpaceAt_comp_mul_right_mem
import Theorems.Thm_AutomorphicForm_isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_shapedRaw_bundle_sub_translate_unipotent_transl_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply"
p2m_attr_erase "simp" "Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

noncomputable section

namespace R3bAux

open AdelicDock NumberField.AdelicLevel NumberField.StandardAddChar AutomorphicForm LanglandsTunnell RSCarrier UnramifiedWhittaker

theorem ext_of_glArch_of_glFin {x y : AdelicGL2 (𝓞 ℚ) ℚ}
    (h1 : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h2 : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) h1
  · exact congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) h2

theorem ext_of_glArch_of_localAt {x y : AdelicGL2 (𝓞 ℚ) ℚ}
    (h1 : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v x = localAt ℚ v y) :
    x = y := by
  refine ext_of_glArch_of_glFin h1 (Units.ext (Matrix.ext fun i j => RestrictedProduct.ext _ _ fun v => ?_))
  exact congrArg (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) (h2 v)

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 ℚ) ℚ}
    (ha : glArch (𝓞 ℚ) ℚ a = 1) (hb : glFin (𝓞 ℚ) ℚ b = 1) : a * b = b * a :=
  ext_of_glArch_of_glFin (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (by rw [map_mul, map_mul, hb, one_mul, mul_one])

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    glArch (𝓞 ℚ) ℚ (placeEmbed ℚ v x) = 1 :=
  glArch_finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x)

theorem placeEmbed_mem (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_placeEmbed v x)

theorem localAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v x hw]

theorem placeEmbed_comm {v w : HeightOneSpectrum (𝓞 ℚ)} (hvw : v ≠ w)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (y : GL (Fin 2) (w.adicCompletion ℚ)) :
    placeEmbed ℚ v x * placeEmbed ℚ w y = placeEmbed ℚ w y * placeEmbed ℚ v x := by
  refine ext_of_glArch_of_localAt (by rw [map_mul, map_mul, glArch_placeEmbed, glArch_placeEmbed]) fun q => ?_
  rw [map_mul, map_mul]
  by_cases hqv : q = v
  · subst hqv
    rw [localAt_placeEmbed_self, localAt_placeEmbed_of_ne hvw, mul_one, one_mul]
  · rw [localAt_placeEmbed_of_ne hqv, one_mul, mul_one]

theorem mul_placeEmbed_mul_placeEmbed_of_ne (g : AdelicGL2 (𝓞 ℚ) ℚ) {v w : HeightOneSpectrum (𝓞 ℚ)} (hvw : v ≠ w)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (y : GL (Fin 2) (w.adicCompletion ℚ)) :
    g * placeEmbed ℚ v x * placeEmbed ℚ w y = g * placeEmbed ℚ w y * placeEmbed ℚ v x := by
  rw [mul_assoc, placeEmbed_comm hvw, ← mul_assoc]

theorem ratArchGL2_mul (g h : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  simp only [ratArchGL2, map_mul]

theorem ratArchGL2_eq_one_of_mem {a : AdelicGL2 (𝓞 ℚ) ℚ} (ha : a ∈ finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 a = 1 := by
  simp only [ratArchGL2, (mem_finiteAdelicGL2Subgroup_iff ℚ a).mp ha, map_one]

theorem ratArchGL2_mul_of_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) {a : AdelicGL2 (𝓞 ℚ) ℚ} (ha : a ∈ finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (g * a) = ratArchGL2 g := by
  rw [ratArchGL2_mul, ratArchGL2_eq_one_of_mem ha, mul_one]

theorem coe_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem finFactor_mul_of_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) {a : AdelicGL2 (𝓞 ℚ) ℚ} (ha : a ∈ finiteAdelicGL2Subgroup ℚ) :
    finFactor (g * a) = finFactor g * ⟨a, ha⟩ := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, coe_finFactor, coe_finFactor, ratArchGL2_mul_of_mem g ha, mul_assoc]

theorem finFactor_coe (a : finiteAdelicGL2Subgroup ℚ) : finFactor (a : AdelicGL2 (𝓞 ℚ) ℚ) = a := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_eq_one_of_mem a.2, map_one, inv_one, one_mul]

theorem finFactor_coe_finFactor_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) {a : AdelicGL2 (𝓞 ℚ) ℚ} (ha : a ∈ finiteAdelicGL2Subgroup ℚ) :
    finFactor ((finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * a) = finFactor (g * a) := by
  rw [finFactor_mul_of_mem _ ha, finFactor_coe, finFactor_mul_of_mem _ ha]

theorem glFin_archRealGLAt (h : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem ratArchGL2_archRealGLAt (h : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h) = h := by
  have e : glArch (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h) =
      archGLIncl ℚ default (glEquivOfRingEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm h) :=
    glArch_adelicArchGLIncl ℚ _
  unfold ratArchGL2
  rw [e, archComponent_archGLIncl_self]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
      (((glEquivOfRingEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm h :
        GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) i j) =
      (h : Matrix (Fin 2) (Fin 2) ℝ) i j
  rw [glEquivOfRingEquiv_apply_entry]
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).apply_symm_apply _

theorem coe_mul_archRealGLAt (a : finiteAdelicGL2Subgroup ℚ) (h : GL (Fin 2) ℝ) :
    (a : AdelicGL2 (𝓞 ℚ) ℚ) * archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h =
      archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h * a :=
  mul_comm_of_glArch_eq_one_of_glFin_eq_one ((mem_finiteAdelicGL2Subgroup_iff ℚ _).mp a.2) (glFin_archRealGLAt h)

theorem ratArchGL2_archRealGLAt_mul_coe (h : GL (Fin 2) ℝ) (a : finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h * a) = h := by
  rw [ratArchGL2_mul_of_mem _ a.2, ratArchGL2_archRealGLAt]

theorem finFactor_archRealGLAt_mul_coe (h : GL (Fin 2) ℝ) (a : finiteAdelicGL2Subgroup ℚ) :
    finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h * a) = a := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_archRealGLAt_mul_coe, inv_mul_cancel_left]

theorem coe_mul_adelicArchGLInclAt (a : finiteAdelicGL2Subgroup ℚ) (w : InfinitePlace ℚ) (k : GL (Fin 2) w.Completion) :
    (a : AdelicGL2 (𝓞 ℚ) ℚ) * adelicArchGLInclAt ℚ w k = adelicArchGLInclAt ℚ w k * a :=
  mul_comm_of_glArch_eq_one_of_glFin_eq_one ((mem_finiteAdelicGL2Subgroup_iff ℚ _).mp a.2) (glFin_adelicArchGLIncl ℚ _)

theorem globalPoints_unipotentGL2 (β : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 β) = unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((unipotentGL2 β : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem norm_exp_neg_two_pi_I_mul_ofReal (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [show -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_psiPadicFun {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ‖psiPadicFun x‖ = 1 := by
  obtain ⟨a, k, ha⟩ := exists_pPow_approx x
  rw [psiPadicFun_eq ha, show ((a : ℂ) / (p : ℂ) ^ k) = (((a : ℝ) / (p : ℝ) ^ k : ℝ) : ℂ) by push_cast; ring]
  exact norm_exp_neg_two_pi_I_mul_ofReal _

theorem norm_psiV (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : ‖psiV v x‖ = 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  rw [psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun _

theorem norm_psiFin (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : ‖psiFin x‖ = 1 := by
  rw [psiFin_apply, finprod_eq_prod_of_mulSupport_subset _ (s := (mulSupport_psiV_finite x).toFinset)
    (by intro v hv; simpa using hv), norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiV v _

theorem norm_psiArch (x : InfiniteAdeleRing ℚ) : ‖psiArch x‖ = 1 := by
  rw [psiArch_apply, finprod_eq_prod_of_fintype, norm_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [psiArchPlace_apply, show (2 * Real.pi * Complex.I) *
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (x v) : ℝ) : ℂ) =
      ((2 * Real.pi * (InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (x v) : ℝ) : ℝ) : ℂ) *
        Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_psiQ (x : AdeleRing (𝓞 ℚ) ℚ) : ‖psiQ x‖ = 1 := by
  rw [psiQ_apply, norm_mul, norm_psiArch, norm_psiFin, mul_one]

end R3bAux

end

namespace R3bAux
open AdelicDock NumberField.AdelicLevel NumberField.StandardAddChar AutomorphicForm LanglandsTunnell RSCarrier UnramifiedWhittaker

theorem mul_archRealGLAt_comm_of_mem {a : AdelicGL2 (𝓞 ℚ) ℚ} (ha : a ∈ finiteAdelicGL2Subgroup ℚ) (h : GL (Fin 2) ℝ) :
    a * archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h =
      archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h * a :=
  mul_comm_of_glArch_eq_one_of_glFin_eq_one ((mem_finiteAdelicGL2Subgroup_iff ℚ _).mp ha) (glFin_archRealGLAt h)

theorem mul_adelicArchGLInclAt_comm_of_mem {a : AdelicGL2 (𝓞 ℚ) ℚ} (ha : a ∈ finiteAdelicGL2Subgroup ℚ)
    (w : InfinitePlace ℚ) (k : GL (Fin 2) w.Completion) :
    a * adelicArchGLInclAt ℚ w k = adelicArchGLInclAt ℚ w k * a :=
  mul_comm_of_glArch_eq_one_of_glFin_eq_one ((mem_finiteAdelicGL2Subgroup_iff ℚ _).mp ha) (glFin_adelicArchGLIncl ℚ _)

theorem whittakerCoefficient_unipotentGL2_mul_general (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hper : ∀ (β : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + x) * g) = φ (unipotentGL2 x * g))
    (α : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ α (unipotentGL2 x * g) =
      psiQ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x) * whittakerCoefficient ℚ (productionPinsGeneral ℚ) psiQ φ α g :=
  AutomorphicForm.whittakerCoefficient_unipotentGL2_mul ℚ _ _ _ psiQ psiQ_algebraMap φ g hper α x

end R3bAux

namespace R3bStep
open AdelicDock NumberField.AdelicLevel NumberField.StandardAddChar AutomorphicForm LanglandsTunnell RSCarrier UnramifiedWhittaker

noncomputable def φsh (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (x₀ : p.adicCompletion ℚ) :
    AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g)

noncomputable def Wsh (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (x₀ : p.adicCompletion ℚ) :
    finiteAdelicGL2Subgroup ℚ → ℂ :=
  (fun g : finiteAdelicGL2Subgroup ℚ => Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g)

theorem pe_mem (p : HeightOneSpectrum (𝓞 ℚ)) (x₀ : p.adicCompletion ℚ) :
    placeEmbed ℚ p (unipotent x₀) ∈ finiteAdelicGL2Subgroup ℚ := R3bAux.placeEmbed_mem p _

theorem φsh_apply (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (x₀ : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    φsh φ p x₀ g = φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g := rfl

theorem Wsh_finFactor (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (x₀ : p.adicCompletion ℚ)
    (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    Wsh Wf p x₀ (finFactor X) = Wf (finFactor (X * placeEmbed ℚ p (unipotent x₀))) - Wf (finFactor X) := by
  show Wf (finFactor ((finFactor X : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf (finFactor X) = _
  rw [R3bAux.finFactor_coe_finFactor_mul X (pe_mem p x₀)]

theorem Wsh_apply (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (x₀ : p.adicCompletion ℚ)
    (g : finiteAdelicGL2Subgroup ℚ) :
    Wsh Wf p x₀ g = Wf (g * ⟨placeEmbed ℚ p (unipotent x₀), pe_mem p x₀⟩) - Wf g := by
  show Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g = _
  rw [R3bAux.finFactor_mul_of_mem _ (pe_mem p x₀), R3bAux.finFactor_coe]

end R3bStep

theorem R3bStep.c1
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h1 : Continuous φ) :
    Continuous (R3bStep.φsh φ p x₀) := by
  exact (AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate ℚ φ (placeEmbed ℚ p (unipotent x₀))).1 h1

theorem R3bStep.c2s
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hcont₀ : Continuous φ₀)
    (hcusp₀ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₀)
    (hrep₀ : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₀ α = φ₀)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h2 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ)
    (t3 : (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ = fun x => ∑ i, c i * φ₀ (x * g i)))
    (h5 : (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 0 g = 0))
    (h15 : (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g)) :
    IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (R3bStep.φsh φ p x₀) := by
  obtain ⟨m, c, g, hg, hφ⟩ := t3
  have T := AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate ℚ φ (placeEmbed ℚ p (unipotent x₀))

  have hA := (AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _).mp h2.1
  obtain ⟨⟨hleft, hcentral⟩, hmem⟩ := hA
  refine ⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _).mpr ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·
    exact T.2.2.1 hleft
  ·
    intro z x
    show φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x * placeEmbed ℚ p (unipotent x₀)) - φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * x) =
      ((ξ z : ℂˣ) : ℂ) * (φ (x * placeEmbed ℚ p (unipotent x₀)) - φ x)
    rw [mul_assoc, hcentral, hcentral, mul_sub]
  ·
    have hterm : ∀ i, MemLp (fun x : AdelicGL2 (𝓞 ℚ) ℚ => c i * φ₀ (x * (placeEmbed ℚ p (unipotent x₀) * g i))) 2
        ((productionPinsGeneral ℚ).μ.restrict (productionPinsGeneral ℚ).D) := by
      intro i
      have hG := (AutomorphicForm.isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat ξ φ₀ hcusp₀ hcont₀ hrep₀
        (placeEmbed ℚ p (unipotent x₀) * g i)).1
      have hM := ((AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _).mp hG.1).2
      exact hM.const_mul (c i)
    have hsum := MeasureTheory.memLp_finset_sum' (s := Finset.univ) (fun i _ => hterm i)
    have heq : R3bStep.φsh φ p x₀ = (∑ i ∈ Finset.univ, fun x : AdelicGL2 (𝓞 ℚ) ℚ => c i * φ₀ (x * (placeEmbed ℚ p (unipotent x₀) * g i))) - φ := by
      funext x
      show φ (x * placeEmbed ℚ p (unipotent x₀)) - φ x = _
      rw [Pi.sub_apply, Finset.sum_apply, hφ]
      simp only [mul_assoc]
    rw [heq]
    exact hsum.sub hmem
  ·
    intro x
    have e := (T.2.2.2.2.1 (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ 0 x (h15 0 _) (h15 0 x)).2
    rw [h5, h5, sub_self, AutomorphicForm.whittakerCoefficient_zero_eq_constantTerm] at e
    exact e

theorem R3bStep.c3s
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (t3 : (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ = fun x => ∑ i, c i * φ₀ (x * g i))) :
    (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
        (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ (R3bStep.φsh φ p x₀) = fun x => ∑ i, c i * φ₀ (x * g i)) := by
  obtain ⟨m, c, g, hg, hφ⟩ := t3
  refine ⟨m + m, Fin.append c (fun i => - c i), Fin.append (fun i => placeEmbed ℚ p (unipotent x₀) * g i) (fun i => g i), ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact mul_mem (R3bStep.pe_mem p x₀) (hg j)
    · rw [Fin.append_right]; exact hg j
  · funext x
    show φ (x * placeEmbed ℚ p (unipotent x₀)) - φ x = _
    rw [Fin.sum_univ_add, hφ]
    simp only [Fin.append_left, Fin.append_right, mul_assoc, neg_mul, Finset.sum_neg_distrib]
    ring

theorem R3bStep.c4
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h4 : (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ g)) :
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), (R3bStep.φsh φ p x₀) (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * (R3bStep.φsh φ p x₀) g) := by
  intro z g
  show φ (centralScalar (𝓞 ℚ) ℚ z * g * placeEmbed ℚ p (unipotent x₀)) - φ (centralScalar (𝓞 ℚ) ℚ z * g) =
    ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * (φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g)
  rw [mul_assoc, h4, h4, mul_sub]

theorem R3bStep.c5
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h5 : (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 0 g = 0))
    (h15 : (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g)) :
    (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (R3bStep.φsh φ p x₀) 0 g = 0) := by
  intro g
  have T := (AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate ℚ φ (placeEmbed ℚ p (unipotent x₀))).2.2.2.2.1
  have e := (T (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ 0 g (h15 0 _) (h15 0 g)).2
  rw [h5, h5, sub_self] at e
  exact e

theorem R3bStep.c6
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h6 : (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g‖))
    (h15 : (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g)) :
    (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (R3bStep.φsh φ p x₀) a g‖) := by
  intro g
  have T := (AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate ℚ φ (placeEmbed ℚ p (unipotent x₀))).2.2.2.2.2.1
  exact T (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ g (fun a => h15 a _) (fun a => h15 a g) (h6 _) (h6 g)

theorem R3bStep.c7
    (WA₀ : GL (Fin 2) ℝ → ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h7 : (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g)))
    (h15 : (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g)) :
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (R3bStep.φsh φ p x₀) 1 g = WA₀ (ratArchGL2 g) * (R3bStep.Wsh Wf p x₀) (finFactor g)) := by
  intro g
  have T := (AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate ℚ φ (placeEmbed ℚ p (unipotent x₀))).2.2.2.2.2.2
  have e : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (R3bStep.φsh φ p x₀) 1 g =
      WA₀ (ratArchGL2 g) * (Wf (finFactor g * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)) - Wf (finFactor g)) :=
    T (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ 1 ratArchGL2 finFactor (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ) WA₀ Wf
      (fun g => R3bAux.ratArchGL2_mul_of_mem g (R3bStep.pe_mem p x₀)) (fun g => R3bAux.finFactor_mul_of_mem g (R3bStep.pe_mem p x₀))
      (fun g => h15 1 g) h7 g
  rw [e, R3bStep.Wsh_finFactor, R3bAux.finFactor_mul_of_mem g (R3bStep.pe_mem p x₀)]

theorem R3bStep.c8
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h8 : Measurable Wf) :
    Measurable (R3bStep.Wsh Wf p x₀) := by
  rw [show R3bStep.Wsh Wf p x₀ = fun g => Wf (g * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)) - Wf g from funext (R3bStep.Wsh_apply Wf p x₀)]
  exact (h8.comp (continuous_mul_const _).measurable).sub h8

theorem R3bStep.law
    (WA₀ : GL (Fin 2) ℝ → ℂ) (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (h2 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ)
    (h7 : (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g))) (n : RSCarrier.finUnipotent) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ G : finiteAdelicGL2Subgroup ℚ, Wf ((n : finiteAdelicGL2Subgroup ℚ) * G) = c * Wf G := by
  obtain ⟨h₀, hh₀⟩ := hWA₀
  obtain ⟨⟨hleft, -⟩, -⟩ := h2.1
  have hper : ∀ (G : AdelicGL2 (𝓞 ℚ) ℚ) (β : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + x) * G) = φ (unipotentGL2 x * G) := by
    intro G β x
    rw [unipotentGL2_add, mul_assoc, ← R3bAux.globalPoints_unipotentGL2, hleft]
  obtain ⟨Xm, hXm⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp n.2)
  refine ⟨NumberField.StandardAddChar.psiQ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * Xm.toAdd), R3bAux.norm_psiQ _, fun G => ?_⟩
  have hnX : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 Xm.toAdd := hXm.symm
  have e1 := h7 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (G : AdelicGL2 (𝓞 ℚ) ℚ))
  rw [R3bAux.ratArchGL2_archRealGLAt_mul_coe, R3bAux.finFactor_archRealGLAt_mul_coe] at e1
  have e2 := h7 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (((n : finiteAdelicGL2Subgroup ℚ) * G : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))
  rw [R3bAux.ratArchGL2_archRealGLAt_mul_coe, R3bAux.finFactor_archRealGLAt_mul_coe] at e2
  have e3 := R3bAux.whittakerCoefficient_unipotentGL2_mul_general φ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (G : AdelicGL2 (𝓞 ℚ) ℚ)) (hper _) 1 Xm.toAdd
  have e4 : unipotentGL2 Xm.toAdd * (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (G : AdelicGL2 (𝓞 ℚ) ℚ)) =
      archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h₀ * (((n : finiteAdelicGL2Subgroup ℚ) * G : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := by
    rw [← hnX, Subgroup.coe_mul, ← mul_assoc, R3bAux.mul_archRealGLAt_comm_of_mem (n : finiteAdelicGL2Subgroup ℚ).2, mul_assoc]
  rw [e4, e2, e1] at e3
  exact mul_left_cancel₀ hh₀ (e3.trans (mul_left_comm _ _ _))

theorem R3bStep.c9
    (WA₀ : GL (Fin 2) ℝ → ℂ)
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h2 : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ)
    (h7 : (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g))) :
    (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖(R3bStep.Wsh Wf p x₀) ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖(R3bStep.Wsh Wf p x₀) g‖) := by
  intro n g
  obtain ⟨c, hc1, hc⟩ := R3bStep.law WA₀ hWA₀ ξ φ Wf h2 h7 n
  rw [R3bStep.Wsh_apply, R3bStep.Wsh_apply, mul_assoc, hc (g * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)), hc g, ← mul_sub, norm_mul, hc1, one_mul]

theorem R3bStep.c10
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h10 : (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf (g * u) = Wf g)) :
    (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → (R3bStep.Wsh Wf p x₀) (g * u) = (R3bStep.Wsh Wf p x₀) g) := by
  obtain ⟨U, hUo, hUinv⟩ := h10
  refine ⟨U ⊓ U.comap (MulAut.conj (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)⁻¹).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.coe_inf, Subgroup.coe_comap]
    exact hUo.inter (hUo.preimage ((continuous_const_mul _).mul continuous_const))
  · intro g k hk
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk2
    rw [R3bStep.Wsh_apply, R3bStep.Wsh_apply, hUinv g k hk1,
      show g * k * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ) = g * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ) * ((⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)⁻¹ * k * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)) by group,
      hUinv _ _ hk2]

theorem R3bStep.c11
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h11 : (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
          (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
          (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
          (∃ r : v.adicCompletionIntegers ℚ,
            ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
              algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
          ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          (R3bStep.Wsh Wf p x₀) (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * (R3bStep.Wsh Wf p x₀) (finFactor g)) := by
  intro v
  obtain ⟨ψ, e1, e2, e3, e4⟩ := h11 v
  refine ⟨ψ, e1, e2, e3, fun x g => ?_⟩
  rw [R3bStep.Wsh_finFactor, R3bStep.Wsh_finFactor, mul_assoc, e4, e4, mul_sub]

theorem R3bStep.c12
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h12 : (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
          (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ p h))) ∈
            AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀)) :
    (∀ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ q g = 1 →
        (fun h : GL (Fin 2) (q.adicCompletion ℚ) => (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ q h))) ∈
          AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ q φ₀) := by
  intro q g hg
  by_cases hqp : q = p
  · subst hqp
    have hmem := h12 q g hg
    have htr := AutomorphicForm.WhittakerModel.localSpaceAt_comp_mul_right_mem (productionPinsGeneral ℚ)
      NumberField.StandardAddChar.psiQ q φ₀ _ hmem (unipotent x₀)
    have hfun : (fun h : GL (Fin 2) (q.adicCompletion ℚ) => R3bStep.Wsh Wf q x₀ (finFactor (g * placeEmbed ℚ q h))) =
        (fun h : GL (Fin 2) (q.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ q (h * unipotent x₀)))) -
          (fun h : GL (Fin 2) (q.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ q h))) := by
      funext h
      rw [Pi.sub_apply, R3bStep.Wsh_finFactor, map_mul, mul_assoc]
    rw [hfun]
    exact Submodule.sub_mem _ htr hmem
  · have hg' : localAt ℚ q (g * placeEmbed ℚ p (unipotent x₀)) = 1 := by
      rw [map_mul, hg, R3bAux.localAt_placeEmbed_of_ne hqp, one_mul]
    have hfun : (fun h : GL (Fin 2) (q.adicCompletion ℚ) => R3bStep.Wsh Wf p x₀ (finFactor (g * placeEmbed ℚ q h))) =
        (fun h : GL (Fin 2) (q.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ p (unipotent x₀) * placeEmbed ℚ q h))) -
          (fun h : GL (Fin 2) (q.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ q h))) := by
      funext h
      rw [Pi.sub_apply, R3bStep.Wsh_finFactor, R3bAux.mul_placeEmbed_mul_placeEmbed_of_ne g hqp]
    rw [hfun]
    exact Submodule.sub_mem _ (h12 q _ hg') (h12 q g hg)

theorem R3bStep.c13
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h13 : (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ g)) :
    (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → (R3bStep.φsh φ p x₀) (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = (R3bStep.φsh φ p x₀) g) := by
  obtain ⟨U', hU'o, hU'inv⟩ := h13
  refine ⟨U' ⊓ U'.comap (MulAut.conj (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)⁻¹).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.coe_inf, Subgroup.coe_comap]
    exact hU'o.inter (hU'o.preimage ((continuous_const_mul _).mul continuous_const))
  · intro g k hk
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hk2
    have e := hU'inv (g * placeEmbed ℚ p (unipotent x₀)) _ hk2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at e
    show φ (g * k * placeEmbed ℚ p (unipotent x₀)) - φ (g * k) = φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g
    rw [hU'inv g k hk1, show g * (k : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀) =
        g * placeEmbed ℚ p (unipotent x₀) * ((↑(⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ))⁻¹ * ↑k * ↑(⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)) by
          simp only [mul_assoc, mul_inv_cancel_left], e]

theorem R3bStep.c14
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h14 : (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
          (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ)) :
    (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
        (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) (R3bStep.φsh φ p x₀)) := by
  obtain ⟨n, hn⟩ := h14
  refine ⟨n, fun k g => ?_⟩
  show φ (g * adelicArchGLInclAt ℚ default (k : GL (Fin 2) (default : InfinitePlace ℚ).Completion) * placeEmbed ℚ p (unipotent x₀)) -
      φ (g * adelicArchGLInclAt ℚ default (k : GL (Fin 2) (default : InfinitePlace ℚ).Completion)) =
    ((archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n k : ℂˣ) : ℂ) * (φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g)
  rw [mul_assoc, ← R3bAux.mul_adelicArchGLInclAt_comm_of_mem (R3bStep.pe_mem p x₀), ← mul_assoc, hn k (g * placeEmbed ℚ p (unipotent x₀)), hn k g, mul_sub]

theorem R3bStep.c15
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (h15 : (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g)) :
    (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (R3bStep.φsh φ p x₀) a g) := by
  intro a g
  have T := (AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate ℚ φ (placeEmbed ℚ p (unipotent x₀))).2.2.2.2.1
  exact (T (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ a g (h15 a _) (h15 a g)).1

theorem R3bStep.o1
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : p ∈ S)
    (x₀ : p.adicCompletion ℚ)
    (o1 : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ v x)) = (R3bStep.Wsh Wf p x₀) (finFactor g)) := by
  intro v hv x g hx
  have hvp : v ≠ p := by rintro rfl; exact hv hp
  rw [R3bStep.Wsh_finFactor, R3bStep.Wsh_finFactor, R3bAux.mul_placeEmbed_mul_placeEmbed_of_ne g hvp, o1 v hv x _ hx, o1 v hv x g hx]

theorem R3bStep.o2
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : p ∈ S)
    (x₀ : p.adicCompletion ℚ)
    (o2 : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (g * placeEmbed ℚ v
            (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf (finFactor g))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = (R3bStep.Wsh Wf p x₀) (finFactor g)) := by
  intro v hv r g
  have hvp : v ≠ p := by rintro rfl; exact hv hp
  rw [R3bStep.Wsh_finFactor, R3bStep.Wsh_finFactor, R3bAux.mul_placeEmbed_mul_placeEmbed_of_ne g hvp, o2 v hv r, o2 v hv r g]

theorem R3bStep.o3
    (Θ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : p ∈ S)
    (x₀ : p.adicCompletion ℚ)
    (o3 : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
            (∑ i, Wf (finFactor (g * placeEmbed ℚ v
                (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
              Wf (finFactor (g * placeEmbed ℚ v
                (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            Θ.a v * Wf (finFactor g))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ i, (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ v
              (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
            (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ v
              (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          Θ.a v * (R3bStep.Wsh Wf p x₀) (finFactor g)) := by
  intro v hv
  have hvp : v ≠ p := by rintro rfl; exact hv hp
  obtain ⟨b, hb⟩ := o3 v hv
  refine ⟨b, fun g => ?_⟩
  simp only [R3bStep.Wsh_finFactor, R3bAux.mul_placeEmbed_mul_placeEmbed_of_ne g hvp, Finset.sum_sub_distrib]
  have H1 := hb (g * placeEmbed ℚ p (unipotent x₀))
  have H2 := hb g
  linear_combination H1 - H2

theorem R3bStep.o4
    (Θ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : p ∈ S)
    (x₀ : p.adicCompletion ℚ)
    (o4 : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf (finFactor (g * placeEmbed ℚ v
            (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf (finFactor g))) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * (R3bStep.Wsh Wf p x₀) (finFactor g)) := by
  intro v hv g
  have hvp : v ≠ p := by rintro rfl; exact hv hp
  rw [R3bStep.Wsh_finFactor, R3bStep.Wsh_finFactor, R3bAux.mul_placeEmbed_mul_placeEmbed_of_ne g hvp, o4 v hv, o4 v hv g, mul_sub]

theorem R3bStep.lev
    (Θ : HeckeEigensystem ℚ ℂ)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hlevel : (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ T → ∀ (k : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level → Wf (finFactor (g * placeEmbed ℚ p k)) = Wf (finFactor g))) :
    ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T → q ≠ p → ∀ (k : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q Θ.level → (R3bStep.Wsh Wf p x₀) (finFactor (g * placeEmbed ℚ q k)) = (R3bStep.Wsh Wf p x₀) (finFactor g) := by
  intro q hqT hqp k g hk
  rw [R3bStep.Wsh_finFactor, R3bStep.Wsh_finFactor, R3bAux.mul_placeEmbed_mul_placeEmbed_of_ne g hqp, hlevel q hqT k _ hk,
    hlevel q hqT k g hk]

theorem R3bStep.sh
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x₀ : p.adicCompletion ℚ)
    (T' : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hpT' : p ∉ T')
    (m : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hshell : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' →
      (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ m q) → n ≠ 0 →
            localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
              unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
            Wf g = 0)) :
    ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' →
      (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ m q) → n ≠ 0 →
          localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
          (R3bStep.Wsh Wf p x₀) g = 0) := by
  intro q hq g x n k hk hn hloc
  have hqp : q ≠ p := by rintro rfl; exact hpT' hq
  rw [R3bStep.Wsh_apply, hshell q hq g x n k hk hn hloc, hshell q hq (g * (⟨placeEmbed ℚ p (unipotent x₀), R3bStep.pe_mem p x₀⟩ : finiteAdelicGL2Subgroup ℚ)) x n k hk hn ?_, sub_self]
  rw [Subgroup.coe_mul, map_mul, hloc]
  show _ * localAt ℚ q (placeEmbed ℚ p (unipotent x₀)) = _
  rw [R3bAux.localAt_placeEmbed_of_ne hqp, mul_one]

theorem solution
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ₀c : Continuous φ₀) (hφ₀ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₀)
    (hrep₀ : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₀ α = φ₀)
    (WA₀ : GL (Fin 2) ℝ → ℂ) (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ S) (x₀ : p.adicCompletion ℚ)
    (T T' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hpT' : p ∉ T') (m : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hinv : Continuous φ ∧
        IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ ∧
        (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
        (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ g) ∧
        (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 0 g = 0) ∧
        (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g‖) ∧
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g)) ∧
        Measurable Wf ∧
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf g‖) ∧
        (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf (g * u) = Wf g) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
          (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
          (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
          (∃ r : v.adicCompletionIntegers ℚ,
            ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
              algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
          ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
        (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
          (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ p h))) ∈
            AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
        (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ g) ∧
        (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
          (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ) ∧
        (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g))
    (hoff : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (g * placeEmbed ℚ v
            (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
            (∑ i, Wf (finFactor (g * placeEmbed ℚ v
                (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
              Wf (finFactor (g * placeEmbed ℚ v
                (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            Θ.a v * Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf (finFactor (g * placeEmbed ℚ v
            (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf (finFactor g)))
    (hlevel : (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ T → ∀ (k : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level → Wf (finFactor (g * placeEmbed ℚ p k)) = Wf (finFactor g)))
    (hshell : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' →
      (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ m q) → n ≠ 0 →
            localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
              unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
            Wf g = 0)) :
    let φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g)
    let Wf' : finiteAdelicGL2Subgroup ℚ → ℂ := (fun g : finiteAdelicGL2Subgroup ℚ => Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g)
    (Continuous φ' ∧
      IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ' ∧
      (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
        (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ' = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ' g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' a g‖) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' 1 g = WA₀ (ratArchGL2 g) * Wf' (finFactor g)) ∧
      Measurable Wf' ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf' g‖) ∧
      (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf' (g * u) = Wf' g) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf' (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf' (finFactor g)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
        (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf' (finFactor (g * placeEmbed ℚ p h))) ∈
          AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
      (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ' (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ' g) ∧
      (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
        (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ') ∧
      (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' a g)) ∧
    ((∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf' (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf' (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf' (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ i, Wf' (finFactor (g * placeEmbed ℚ v
              (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
            Wf' (finFactor (g * placeEmbed ℚ v
              (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          Θ.a v * Wf' (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf' (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf' (finFactor g))) ∧
    (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T → q ≠ p → ∀ (k : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q Θ.level → Wf' (finFactor (g * placeEmbed ℚ q k)) = Wf' (finFactor g)) ∧
    (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' →
      (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ m q) → n ≠ 0 →
          localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
          Wf' g = 0)) := by
  intro φ' Wf'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hinv
  obtain ⟨o1, o2, o3, o4⟩ := hoff
  exact ⟨⟨R3bStep.c1 φ p x₀ h1, R3bStep.c2s ξ φ₀ hφ₀c hφ₀ hrep₀ φ p x₀ h2 h3 h5 h15, R3bStep.c3s φ₀ φ p x₀ h3,
      R3bStep.c4 ξ φ p x₀ h4, R3bStep.c5 φ p x₀ h5 h15, R3bStep.c6 φ p x₀ h6 h15, R3bStep.c7 WA₀ φ Wf p x₀ h7 h15,
      R3bStep.c8 Wf p x₀ h8, R3bStep.c9 WA₀ hWA₀ ξ φ Wf p x₀ h2 h7, R3bStep.c10 Wf p x₀ h10, R3bStep.c11 ϖ Wf p x₀ h11,
      R3bStep.c12 φ₀ Wf p x₀ h12, R3bStep.c13 φ p x₀ h13, R3bStep.c14 φ p x₀ h14, R3bStep.c15 φ p x₀ h15⟩,
    ⟨R3bStep.o1 S Wf p hp x₀ o1, R3bStep.o2 S Wf p hp x₀ o2, R3bStep.o3 Θ S ϖ hπall Wf p hp x₀ o3,
      R3bStep.o4 Θ S ϖ hπall Wf p hp x₀ o4⟩,
    R3bStep.lev Θ Wf p x₀ T hlevel, R3bStep.sh ϖ hπall Wf p x₀ T' hpT' m hshell⟩

#print axioms solution

end S_AutomorphicForm_shapedRaw_bundle_sub_translate_unipotent_transl_rat
end P2MW
export P2MW.S_AutomorphicForm_shapedRaw_bundle_sub_translate_unipotent_transl_rat (solution)
