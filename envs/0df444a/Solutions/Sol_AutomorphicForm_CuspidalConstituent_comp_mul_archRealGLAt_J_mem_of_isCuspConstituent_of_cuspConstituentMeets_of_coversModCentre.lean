-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8e6b07b2-696e-5d40-a007-b31a24aac164

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open AutomorphicForm.CuspidalConstituent AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

noncomputable section

namespace K1Chi

variable (F : Type) [Field F] [NumberField F]

theorem J_mul_J : (UpperHalfPlane.J : GL (Fin 2) ℝ) * UpperHalfPlane.J = 1 := by
  apply Units.ext
  rw [Units.val_mul, UpperHalfPlane.val_J, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isRowIsometry_J : AutomorphicForm.WindowedSiegel.IsRowIsometry (UpperHalfPlane.J : GL (Fin 2) ℝ) := by
  constructor
  · rw [UpperHalfPlane.val_J, Matrix.det_fin_two_of]
    norm_num
  · intro x y
    rw [UpperHalfPlane.val_J]
    simp

def conjJℝ : rowIsometrySubgroup₀ ℝ →* rowIsometrySubgroup₀ ℝ where
  toFun r := ⟨UpperHalfPlane.J * (r : GL (Fin 2) ℝ) * UpperHalfPlane.J, by
    obtain ⟨hd, hiso⟩ := (mem_rowIsometrySubgroup₀_iff ℝ).mp r.2
    refine (mem_rowIsometrySubgroup₀_iff ℝ).mpr ⟨?_, (isRowIsometry_J.mul hiso).mul isRowIsometry_J⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hd, UpperHalfPlane.val_J]
    simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    show UpperHalfPlane.J * 1 * UpperHalfPlane.J = 1
    rw [mul_one, J_mul_J]
  map_mul' r s := by
    apply Subtype.ext
    show UpperHalfPlane.J * ((r : GL (Fin 2) ℝ) * s) * UpperHalfPlane.J =
      UpperHalfPlane.J * r * UpperHalfPlane.J * (UpperHalfPlane.J * s * UpperHalfPlane.J)
    have := J_mul_J
    calc UpperHalfPlane.J * ((r : GL (Fin 2) ℝ) * s) * UpperHalfPlane.J
        = UpperHalfPlane.J * r * (UpperHalfPlane.J * UpperHalfPlane.J) * s * UpperHalfPlane.J := by
          rw [J_mul_J]; group
      _ = UpperHalfPlane.J * r * UpperHalfPlane.J * (UpperHalfPlane.J * s * UpperHalfPlane.J) := by group

theorem coe_conjJℝ (r : rowIsometrySubgroup₀ ℝ) :
    ((conjJℝ r : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) = UpperHalfPlane.J * (r : GL (Fin 2) ℝ) * UpperHalfPlane.J := rfl

variable {F}

theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (y : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm y‖ = ‖y‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm y)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

def conjJc {w : InfinitePlace F} (hw : w.IsReal) :
    rowIsometrySubgroup₀ w.Completion →* rowIsometrySubgroup₀ w.Completion :=
  (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm_ringEquivRealOfIsReal hw)).comp
    (conjJℝ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))

theorem archRealGLAt_glEquiv_symm {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
      (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m)) = archRealGLAt hw m := by
  congr 1
  apply Units.ext
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

theorem rowIsometryInclAt₀_conjJc {w : InfinitePlace F} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ F w (conjJc hw k) =
      archRealGLAt hw UpperHalfPlane.J * rowIsometryInclAt₀ F w k * archRealGLAt hw UpperHalfPlane.J := by
  rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply, ← archRealGLAt_glEquivOfRingEquiv hw,
    ← archRealGLAt_glEquivOfRingEquiv hw (k : GL (Fin 2) w.Completion), ← map_mul, ← map_mul]
  show archRealGLAt hw (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
    (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
      (UpperHalfPlane.J * glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) * UpperHalfPlane.J))) = _
  rw [archRealGLAt_glEquiv_symm]

theorem AJ_mul_AJ {w : InfinitePlace F} (hw : w.IsReal) :
    archRealGLAt hw UpperHalfPlane.J * archRealGLAt hw UpperHalfPlane.J = 1 := by
  rw [← map_mul, J_mul_J, map_one]

theorem AJ_mul_AJ_mul {w : InfinitePlace F} (hw : w.IsReal) (y : AdelicGL2 (𝓞 F) F) :
    archRealGLAt hw UpperHalfPlane.J * (archRealGLAt hw UpperHalfPlane.J * y) = y := by
  rw [← mul_assoc, AJ_mul_AJ, one_mul]

open scoped Classical in

def conjAt {w : InfinitePlace F} (hw : w.IsReal) (v : InfinitePlace F) :
    rowIsometrySubgroup₀ v.Completion →* rowIsometrySubgroup₀ v.Completion :=
  if h : v = w then (by subst h; exact conjJc hw) else MonoidHom.id _

theorem rowIsometryInclAt₀_conjAt {w : InfinitePlace F} (hw : w.IsReal) (v : InfinitePlace F)
    (k : rowIsometrySubgroup₀ v.Completion) :
    rowIsometryInclAt₀ F v (conjAt hw v k) =
      archRealGLAt hw UpperHalfPlane.J * rowIsometryInclAt₀ F v k * archRealGLAt hw UpperHalfPlane.J := by
  classical
  unfold conjAt
  by_cases h : v = w
  · subst h
    rw [dif_pos rfl]
    exact rowIsometryInclAt₀_conjJc hw k
  · rw [dif_neg h, MonoidHom.id_apply]
    have hcomm : Commute (archRealGLAt hw UpperHalfPlane.J) (rowIsometryInclAt₀ F v k) := by
      rw [rowIsometryInclAt₀_apply]
      show Commute (adelicArchGLInclAt F w _) (adelicArchGLInclAt F v _)
      exact (commute_adelicArchGLInclAt_of_ne F h _ _).symm
    rw [hcomm.eq, mul_assoc, AJ_mul_AJ, mul_one]

def RJ {w : InfinitePlace F} (hw : w.IsReal) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun f := fun x => f (x * archRealGLAt hw UpperHalfPlane.J)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem RJ_apply {w : InfinitePlace F} (hw : w.IsReal) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    RJ hw f x = f (x * archRealGLAt hw UpperHalfPlane.J) := rfl

theorem RJ_RJ {w : InfinitePlace F} (hw : w.IsReal) (f : AdelicGL2 (𝓞 F) F → ℂ) : RJ hw (RJ hw f) = f := by
  funext x
  rw [RJ_apply, RJ_apply, mul_assoc, AJ_mul_AJ, mul_one]

def Lt (a : AdelicGL2 (𝓞 F) F) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun f := fun x => f (a * x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Lt_apply (a : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    Lt a f x = f (a * x) := rfl

section TypePieces

variable {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem map_mem_typeSubmodule_of_twist (ι : H →* AdelicGL2 (𝓞 F) F) (ρ : Representation ℂ H W)
    (φ : H →* H) (L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hL : ∀ (u : AdelicGL2 (𝓞 F) F → ℂ) (k : H) (x : AdelicGL2 (𝓞 F) F), L u (x * ι k) = L (fun y => u (y * ι (φ k))) x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ typeSubmodule ι ρ) : L f ∈ typeSubmodule ι (ρ.comp φ) := by
  refine Submodule.span_induction (p := fun f _ => L f ∈ typeSubmodule ι (ρ.comp φ)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι (ρ.comp φ) (L ∘ₗ T) := by
      intro k v x
      show L (T ((ρ.comp φ) k v)) x = L (T v) (x * ι k)
      rw [hL, MonoidHom.comp_apply]
      have : T (ρ (φ k) v) = fun y => T v (y * ι (φ k)) := funext fun y => hT (φ k) v y
      rw [this]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; simp only [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; simp only [map_smul]; exact Submodule.smul_mem _ c ha

end TypePieces

theorem RJ_mem_archTypeSubmoduleAt {w : InfinitePlace F} (hw : w.IsReal) (v : InfinitePlace F) (τ : ArchRepAt F v)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archTypeSubmoduleAt F v τ) :
    RJ hw f ∈ archTypeSubmoduleAt F v ⟨τ.n, τ.ρ.comp (conjAt hw v)⟩ := by
  refine map_mem_typeSubmodule_of_twist (rowIsometryInclAt₀ F v) τ.ρ (conjAt hw v) (RJ hw) ?_ hf
  intro u k x
  rw [RJ_apply, RJ_apply, rowIsometryInclAt₀_conjAt]
  congr 1
  simp only [mul_assoc, AJ_mul_AJ_mul]

theorem Lt_mem_archTypeSubmoduleAt (a : AdelicGL2 (𝓞 F) F) (v : InfinitePlace F) (τ : ArchRepAt F v)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archTypeSubmoduleAt F v τ) :
    Lt a f ∈ archTypeSubmoduleAt F v τ := by
  have h := map_mem_typeSubmodule_of_twist (rowIsometryInclAt₀ F v) τ.ρ (MonoidHom.id _) (Lt a) ?_ hf
  · simp at h
    exact h
  · intro u k x
    rw [Lt_apply, Lt_apply, MonoidHom.id_apply, mul_assoc]

def tysJ {w : InfinitePlace F} (hw : w.IsReal) (tys : ArchTypeFamily F) : ArchTypeFamily F where
  card := tys.card
  rep := fun v i => ⟨(tys.rep v i).n, (tys.rep v i).ρ.comp (conjAt hw v)⟩

theorem RJ_mem_archCutSubmodule {w : InfinitePlace F} (hw : w.IsReal) (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) : RJ hw f ∈ archCutSubmodule F (tysJ hw tys) := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro v
  refine Submodule.iSup_induction _ (motive := fun f => RJ hw f ∈ ⨆ i, archTypeSubmoduleAt F v ((tysJ hw tys).rep v i))
    (hf v) ?_ ?_ ?_
  · intro i f hfi
    exact Submodule.mem_iSup_of_mem i (RJ_mem_archTypeSubmoduleAt hw v _ hfi)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; simp only [map_add]; exact Submodule.add_mem _ ha hb

theorem Lt_mem_archCutSubmodule (a : AdelicGL2 (𝓞 F) F) (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) : Lt a f ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro v
  refine Submodule.iSup_induction _ (motive := fun f => Lt a f ∈ ⨆ i, archTypeSubmoduleAt F v (tys.rep v i))
    (hf v) ?_ ?_ ?_
  · intro i f hfi
    exact Submodule.mem_iSup_of_mem i (Lt_mem_archTypeSubmoduleAt a v _ hfi)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; simp only [map_add]; exact Submodule.add_mem _ ha hb

theorem dual_comp {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (φ : H →* H) :
    Representation.dual (ρ.comp φ) = (Representation.dual ρ).comp φ := by
  apply MonoidHom.ext
  intro g
  simp only [Representation.dual_apply, MonoidHom.comp_apply, map_inv]

theorem RJ_mem_archDualTypeSubmoduleAt {w : InfinitePlace F} (hw : w.IsReal) (v : InfinitePlace F) (τ : ArchRepAt F v)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualTypeSubmoduleAt F v τ) :
    RJ hw f ∈ archDualTypeSubmoduleAt F v ⟨τ.n, τ.ρ.comp (conjAt hw v)⟩ := by
  show RJ hw f ∈ typeSubmodule (rowIsometryInclAt₀ F v) (Representation.dual (τ.ρ.comp (conjAt hw v)))
  rw [dual_comp]
  refine map_mem_typeSubmodule_of_twist (rowIsometryInclAt₀ F v) (Representation.dual τ.ρ) (conjAt hw v) (RJ hw) ?_ hf
  intro u k x
  rw [RJ_apply, RJ_apply, rowIsometryInclAt₀_conjAt]
  congr 1
  simp only [mul_assoc, AJ_mul_AJ_mul]

theorem Lt_mem_archDualTypeSubmoduleAt (a : AdelicGL2 (𝓞 F) F) (v : InfinitePlace F) (τ : ArchRepAt F v)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualTypeSubmoduleAt F v τ) :
    Lt a f ∈ archDualTypeSubmoduleAt F v τ := by
  have h := map_mem_typeSubmodule_of_twist (rowIsometryInclAt₀ F v) (Representation.dual τ.ρ) (MonoidHom.id _) (Lt a) ?_ hf
  · simp at h
    exact h
  · intro u k x
    rw [Lt_apply, Lt_apply, MonoidHom.id_apply, mul_assoc]

theorem RJ_mem_archDualCutSubmodule {w : InfinitePlace F} (hw : w.IsReal) (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) : RJ hw f ∈ archDualCutSubmodule F (tysJ hw tys) := by
  unfold archDualCutSubmodule at hf ⊢
  rw [Submodule.mem_iInf] at hf ⊢
  intro v
  refine Submodule.iSup_induction _ (motive := fun f => RJ hw f ∈ ⨆ i, archDualTypeSubmoduleAt F v ((tysJ hw tys).rep v i))
    (hf v) ?_ ?_ ?_
  · intro i f hfi
    exact Submodule.mem_iSup_of_mem i (RJ_mem_archDualTypeSubmoduleAt hw v _ hfi)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; simp only [map_add]; exact Submodule.add_mem _ ha hb

theorem Lt_mem_archDualCutSubmodule (a : AdelicGL2 (𝓞 F) F) (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) : Lt a f ∈ archDualCutSubmodule F tys := by
  unfold archDualCutSubmodule at hf ⊢
  rw [Submodule.mem_iInf] at hf ⊢
  intro v
  refine Submodule.iSup_induction _ (motive := fun f => Lt a f ∈ ⨆ i, archDualTypeSubmoduleAt F v (tys.rep v i))
    (hf v) ?_ ?_ ?_
  · intro i f hfi
    exact Submodule.mem_iSup_of_mem i (Lt_mem_archDualTypeSubmoduleAt a v _ hfi)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; simp only [map_add]; exact Submodule.add_mem _ ha hb

section TestFn

variable {w : InfinitePlace F} (hw : w.IsReal)

def Jinf : GL (Fin 2) (InfiniteAdeleRing F) := glArch (𝓞 F) F (archRealGLAt hw UpperHalfPlane.J)

theorem Jinf_eq : Jinf hw = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm UpperHalfPlane.J) :=
  glArch_adelicArchGLIncl F _

theorem glFin_AJ : glFin (𝓞 F) F (archRealGLAt hw UpperHalfPlane.J) = 1 := glFin_adelicArchGLIncl F _

def dJ (i : Fin 2) : InfiniteAdeleRing F := ((Jinf hw : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) _) i i

theorem Jinf_coe_eq_diagonal :
    ((Jinf hw : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = Matrix.diagonal (dJ hw) := by
  ext i j
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq]; rfl
  · rw [Matrix.diagonal_apply_ne _ hij, Jinf_eq]
    show archMatrixUpdate F w ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm UpperHalfPlane.J : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = 0
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry, UpperHalfPlane.val_J]
      have hJ : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j = 0 := by
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
      show (ringEquivRealOfIsReal hw).symm ((!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) = 0
      rw [hJ, map_zero]
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv, Matrix.one_apply_ne hij]
      rfl

theorem archEntries_conj (m : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2) :
    archEntries F (Jinf hw * m * Jinf hw) i j =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (dJ hw i) * archEntries F m i j *
        InfiniteAdeleRing.ringEquiv_mixedSpace F (dJ hw j) := by
  rw [archEntries_apply, archEntries_apply, Units.val_mul, Units.val_mul, Jinf_coe_eq_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul, map_mul, map_mul]

open scoped Classical in

theorem isArchTestFactor_conj {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun m => fa (Jinf hw * m * Jinf hw)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun e => Φ (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F (dJ hw i) * e i j *
      InfiniteAdeleRing.ringEquiv_mixedSpace F (dJ hw j)), ?_, ?_⟩, ?_⟩
  · refine hΦ.comp ?_
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    exact (contDiff_const.mul (contDiff_apply_apply (𝕜 := ℝ) (E := mixedEmbedding.mixedSpace F) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) i j)).mul contDiff_const
  · intro m
    show fa (Jinf hw * m * Jinf hw) = Φ _
    rw [hfaΦ]
    congr 1
    funext i j
    exact archEntries_conj hw m i j
  · have : (fun m => fa (Jinf hw * m * Jinf hw)) = fa ∘ ((Homeomorph.mulLeft (Jinf hw)).trans (Homeomorph.mulRight (Jinf hw))) := by
      funext m; rfl
    rw [this]
    exact hsupp.comp_homeomorph _

def conjFn (f : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => f (archRealGLAt hw UpperHalfPlane.J * y * archRealGLAt hw UpperHalfPlane.J)

theorem conjFn_apply (f : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) :
    conjFn hw f y = f (archRealGLAt hw UpperHalfPlane.J * y * archRealGLAt hw UpperHalfPlane.J) := rfl

theorem isFactorizableTestFn_conjFn {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (conjFn hw f) := by
  obtain ⟨fa, ff, hfa, hff, hfac⟩ := hf
  refine ⟨fun m => fa (Jinf hw * m * Jinf hw), ff, isArchTestFactor_conj hw hfa, hff, fun y => ?_⟩
  rw [conjFn_apply, hfac, map_mul, map_mul, map_mul, map_mul, glFin_AJ, one_mul, mul_one]
  rfl

theorem conjFn_eq (f : AdelicGL2 (𝓞 F) F → ℂ) : conjFn hw f = Lt (archRealGLAt hw UpperHalfPlane.J) (RJ hw f) := by
  funext y; rfl

theorem isArchBiFinite_conjFn {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsArchBiFinite F tys f) :
    IsArchBiFinite F (tysJ hw tys) (conjFn hw f) := by
  obtain ⟨h1, h2⟩ := hf
  constructor
  · have heq : (fun x => conjFn hw f x⁻¹) = Lt (archRealGLAt hw UpperHalfPlane.J) (RJ hw (fun x => f x⁻¹)) := by
      funext x
      rw [conjFn_apply, Lt_apply, RJ_apply, mul_inv_rev, mul_inv_rev]
      congr 1
      have hinv : (archRealGLAt hw UpperHalfPlane.J)⁻¹ = archRealGLAt hw UpperHalfPlane.J :=
        inv_eq_of_mul_eq_one_right (AJ_mul_AJ hw)
      rw [hinv, mul_assoc]
    rw [heq]
    exact Lt_mem_archCutSubmodule _ _ (RJ_mem_archCutSubmodule hw tys h1)
  · rw [conjFn_eq]
    exact Lt_mem_archDualCutSubmodule _ _ (RJ_mem_archDualCutSubmodule hw tys h2)

end TestFn

section Haar

open MeasureTheory MeasureTheory.Measure

variable {w : InfinitePlace F} (hw : w.IsReal)

def conjHomeo : AdelicGL2 (𝓞 F) F ≃ₜ AdelicGL2 (𝓞 F) F :=
  (Homeomorph.mulLeft (archRealGLAt hw UpperHalfPlane.J)).trans (Homeomorph.mulRight (archRealGLAt hw UpperHalfPlane.J))

theorem conjHomeo_apply (x : AdelicGL2 (𝓞 F) F) :
    conjHomeo hw x = archRealGLAt hw UpperHalfPlane.J * x * archRealGLAt hw UpperHalfPlane.J := rfl

def conjEquiv : AdelicGL2 (𝓞 F) F ≃ₜ* AdelicGL2 (𝓞 F) F :=
  ContinuousMulEquiv.mk' (conjHomeo hw) fun x y => by
    rw [conjHomeo_apply, conjHomeo_apply, conjHomeo_apply]
    simp only [mul_assoc, AJ_mul_AJ_mul]

theorem conjEquiv_apply (x : AdelicGL2 (𝓞 F) F) :
    conjEquiv hw x = archRealGLAt hw UpperHalfPlane.J * x * archRealGLAt hw UpperHalfPlane.J := rfl

theorem conjEquiv_conjEquiv (x : AdelicGL2 (𝓞 F) F) : conjEquiv hw (conjEquiv hw x) = x := by
  rw [conjEquiv_apply, conjEquiv_apply]
  simp only [mul_assoc, AJ_mul_AJ_mul]
  rw [AJ_mul_AJ, mul_one]

theorem map_conjEquiv_adelicGLHaar :
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
     Measure.map (conjEquiv hw) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set c := conjEquiv hw with hc
  haveI hreg : μ.Regular := by
    rw [hμ]; unfold AdelicHaar.adelicGLHaar; exact Measure.regular_haarMeasure
  haveI : (Measure.map c μ).Regular := Measure.Regular.map c.toHomeomorph
  have hmeas : Measurable c := c.continuous.measurable
  have hcc : Measure.map c (Measure.map c μ) = μ := by
    rw [Measure.map_map hmeas hmeas]
    have : (c : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) ∘ c = id := funext fun x => conjEquiv_conjEquiv hw x
    rw [this, Measure.map_id]
  set s := haarScalarFactor (Measure.map c μ) μ with hs
  have h1 : Measure.map c μ = s • μ := isMulLeftInvariant_eq_smul_of_regular (Measure.map c μ) μ

  have h2 : μ = (s * s) • μ := by
    calc μ = Measure.map c (Measure.map c μ) := hcc.symm
      _ = Measure.map c (s • μ) := by rw [h1]
      _ = s • Measure.map c μ := Measure.map_smul _ _ _
      _ = s • (s • μ) := by rw [h1]
      _ = (s * s) • μ := smul_smul _ _ _
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  have hKpos : 0 < μ K := lt_of_lt_of_le (IsOpen.measure_pos μ isOpen_interior ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩)
    (measure_mono interior_subset)
  have hKtop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have hss : s * s = 1 := by
    have h3 := congrArg (fun ν : Measure (AdelicGL2 (𝓞 F) F) => ν K) h2
    simp only [Measure.smul_apply] at h3
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    have h4 : (1 : ENNReal) * μ K = ((s * s : NNReal) : ENNReal) * μ K := by rw [one_mul]; exact h3
    have h5 := (ENNReal.mul_left_inj hKpos.ne' hKtop).mp h4
    exact_mod_cast h5.symm
  have hs1 : s = 1 := by
    have h := mul_self_eq_one_iff.mp (show ((s : ℝ)) * s = 1 by exact_mod_cast hss)
    rcases h with h | h
    · exact_mod_cast h
    · exfalso; have := s.2; linarith
  rw [h1, hs1, one_smul]

theorem integral_conj (G : AdelicGL2 (𝓞 F) F → ℂ) :
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
     ∫ x, G (archRealGLAt hw UpperHalfPlane.J * x * archRealGLAt hw UpperHalfPlane.J) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
       ∫ x, G x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hme : MeasurableEmbedding (conjEquiv hw) := (conjEquiv hw).toHomeomorph.measurableEmbedding
  have := hme.integral_map (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) G
  rw [map_conjEquiv_adelicGLHaar] at this
  exact this.symm

theorem rightConv_RJ (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (RJ hw φ) f = RJ hw (rightConv F φ (conjFn hw f)) := by
  funext g
  rw [rightConv_apply, RJ_apply, rightConv_apply]
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  rw [← integral_conj hw (fun x => RJ hw φ (g * x) * f x)]
  congr 1
  funext x
  rw [RJ_apply, conjFn_apply]
  congr 2
  simp only [mul_assoc, AJ_mul_AJ_mul]
  rw [AJ_mul_AJ, mul_one]

end Haar

section L2

theorem RJ_eq_rightTranslate {w : InfinitePlace F} (hw : w.IsReal) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    RJ hw f = rightTranslate F (archRealGLAt hw UpperHalfPlane.J) f := rfl

theorem RJ_mem_cuspKFiniteSubmodule {w : InfinitePlace F} (hw : w.IsReal) (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    RJ hw φ ∈ cuspKFiniteSubmodule F pins ξ := by
  refine Submodule.span_induction (p := fun φ _ => RJ hw φ ∈ cuspKFiniteSubmodule F pins ξ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, tys, htys⟩
    refine Submodule.subset_span ⟨?_, ?_, tysJ hw tys, RJ_mem_archCutSubmodule hw tys htys⟩
    · rw [RJ_eq_rightTranslate]
      exact forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate F hsat _
    · rw [RJ_eq_rightTranslate]
      exact continuous_rightTranslate F hcont _
  · show RJ hw 0 ∈ _
    rw [map_zero]; exact Submodule.zero_mem _
  · intro u u' _ _ hu hu'
    show RJ hw (u + u') ∈ _
    rw [map_add]; exact Submodule.add_mem _ hu hu'
  · intro c u _ hu
    show RJ hw (c • u) ∈ _
    rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem rightTranslate_RJ_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F)
    (hg : glArch (𝓞 F) F g = 1) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F g (RJ hw φ) = RJ hw (rightTranslate F g φ) := by
  funext x
  simp only [rightTranslate_apply, RJ_apply, mul_assoc, archRealGLAt_mul_comm_of_glArch_eq_one hw _ hg]

theorem rightTranslate_rowIsometryInclAt₀_RJ {w : InfinitePlace F} (hw : w.IsReal) (v : InfinitePlace F)
    (k : rowIsometrySubgroup₀ v.Completion) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (rowIsometryInclAt₀ F v k) (RJ hw φ) =
      RJ hw (rightTranslate F (rowIsometryInclAt₀ F v (conjAt hw v k)) φ) := by
  funext x
  rw [rightTranslate_apply, RJ_apply, RJ_apply, rightTranslate_apply, rowIsometryInclAt₀_conjAt]
  congr 1
  simp only [mul_assoc, AJ_mul_AJ_mul]

theorem isCuspSubrep_map_RJ {w : InfinitePlace F} (hw : w.IsReal) {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hV : IsCuspSubrep F pins ξ V) :
    IsCuspSubrep F pins ξ (V.map (RJ hw)) where
  le := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact RJ_mem_cuspKFiniteSubmodule hw pins ξ (hV.le hφ)
  rightTranslate_fin_mem := by
    rintro g hg _ ⟨φ, hφ, rfl⟩
    refine ⟨rightTranslate F g φ, hV.rightTranslate_fin_mem g hg φ hφ, ?_⟩
    exact (rightTranslate_RJ_of_glArch_eq_one hw g ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg) φ).symm
  rightTranslate_arch_mem := by
    rintro v k _ ⟨φ, hφ, rfl⟩
    exact ⟨_, hV.rightTranslate_arch_mem v (conjAt hw v k) φ hφ, (rightTranslate_rowIsometryInclAt₀_RJ hw v k φ).symm⟩
  rightConv_mem := by
    rintro f tys hf hbf _ ⟨φ, hφ, rfl⟩
    exact ⟨_, hV.rightConv_mem (conjFn hw f) (tysJ hw tys) (isFactorizableTestFn_conjFn hw hf)
      (isArchBiFinite_conjFn hw hbf) φ hφ, (rightConv_RJ hw φ f).symm⟩

theorem map_RJ_map_RJ {w : InfinitePlace F} (hw : w.IsReal) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    (V.map (RJ hw)).map (RJ hw) = V := by
  have hcomp : (RJ hw).comp (RJ hw) = (LinearMap.id : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] _) := by
    ext f x
    simp [RJ_RJ]
  rw [← Submodule.map_comp, hcomp, Submodule.map_id]

theorem isCuspConstituent_map_RJ {w : InfinitePlace F} (hw : w.IsReal) {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hV : IsCuspConstituent F pins ξ V) :
    IsCuspConstituent F pins ξ (V.map (RJ hw)) := by
  obtain ⟨hsub, hne, hmin⟩ := hV
  refine ⟨isCuspSubrep_map_RJ hw hsub, ?_, fun W hW hWle => ?_⟩
  · intro h
    apply hne
    rw [← map_RJ_map_RJ hw V, h, Submodule.map_bot]
  · have h1 : W.map (RJ hw) ≤ V := by
      rw [← map_RJ_map_RJ hw V]; exact Submodule.map_mono hWle
    rcases hmin _ (isCuspSubrep_map_RJ hw hW) h1 with h | h
    · left; rw [← map_RJ_map_RJ hw W, h, Submodule.map_bot]
    · right; rw [← map_RJ_map_RJ hw W, h]

theorem glArch_heckeGen (v : HeightOneSpectrum (𝓞 F)) : glArch (𝓞 F) F (heckeGen (𝓞 F) F v) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact heckeGenAt_fst _ i j

theorem glArch_eq_one_of_mem_doubleCoset {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)) :
    glArch (𝓞 F) F x = 1 := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2, glArch_heckeGen,
    (mem_finiteAdelicGL2Subgroup_iff F u').mp hu'.2, one_mul, one_mul]

theorem isIsotypicCuspFormAt_RJ {w : InfinitePlace F} (hw : w.IsReal) (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ)
    (hK : φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ) :
    IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ (RJ hw φ) := by
  obtain ⟨-, hsm⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
      F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) ξ φ hK
  have hcomm : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 →
      archRealGLAt hw UpperHalfPlane.J * k = k * archRealGLAt hw UpperHalfPlane.J := fun k hk =>
    archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk
  exact
    { smoothCusp := hsm _
      continuous := by rw [RJ_eq_rightTranslate]; exact continuous_rightTranslate F hφ.continuous _
      level_invariant := fun g u hu => by
        have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu.2
        show φ (g * u * _) = φ (g * _)
        rw [mul_assoc, ← hcomm u hu1, ← mul_assoc, hφ.level_invariant _ u hu]
      hecke_eigen := fun v hv => by
        obtain ⟨reps, hreps, heq⟩ := hφ.hecke_eigen v hv
        refine ⟨reps, hreps, fun g => ?_⟩
        have hk : ∀ i, glArch (𝓞 F) F (reps i) = 1 := fun i =>
          glArch_eq_one_of_mem_doubleCoset (hreps.mem_doubleCoset i)
        show (∑ i, φ (g * reps i * _)) = _ * φ (g * _)
        have := heq (g * archRealGLAt hw UpperHalfPlane.J)
        simp only [SmoothCusp.heckeCosetSum, mul_assoc] at this ⊢
        simpa only [hcomm _ (hk _)] using this
      central_eigen := fun v hv g => by
        show φ (_ * g * _) = _ * φ (g * _)
        rw [mul_assoc]
        exact hφ.central_eigen v hv _ }

theorem cuspConstituentMeets_map_RJ {w : InfinitePlace F} (hw : w.IsReal) (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hV : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (hmeet : CuspConstituentMeets F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V) :
    CuspConstituentMeets F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ (V.map (RJ hw)) := by
  obtain ⟨φ, hφV, hφ0, hiso⟩ := hmeet
  refine ⟨RJ hw φ, Submodule.mem_map_of_mem hφV, ?_, isIsotypicCuspFormAt_RJ hw D ξ N S Ψ hiso (hV.le hφV)⟩
  intro h
  apply hφ0
  rw [← RJ_RJ hw φ, h, map_zero]

end L2

section Assembly

variable {w : InfinitePlace F} (hw : w.IsReal)

theorem RJ_mem_of_constituent_transport (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (hmeet : CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V)
    (hW : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ (V.map (RJ hw)))
    (hWmeet : CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ (V.map (RJ hw)))
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V) :
    (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V := by
  have hWV : V.map (RJ hw) = V :=
    AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre F c u d₁ d₂ T hd hcov ξ N S Ψ _ _
      hW hV hWmeet hmeet
  have : RJ hw x ∈ V.map (RJ hw) := Submodule.mem_map_of_mem hx
  rw [hWV] at this
  exact this

end Assembly

end K1Chi

end

open K1Chi IsDedekindDomain _root_.NumberField _root_.NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion AutomorphicForm.CuspidalConstituent in

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (hmeet : CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V) :
    (fun g => x (g * archRealGLAt hw UpperHalfPlane.J)) ∈ V :=
  RJ_mem_of_constituent_transport hw c u d₁ d₂ T hd hcov ξ N S Ψ V hV hmeet (isCuspConstituent_map_RJ hw hV)
    (cuspConstituentMeets_map_RJ hw _ ξ N S Ψ hV.1 hmeet) x hx

end S_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre (solution)
