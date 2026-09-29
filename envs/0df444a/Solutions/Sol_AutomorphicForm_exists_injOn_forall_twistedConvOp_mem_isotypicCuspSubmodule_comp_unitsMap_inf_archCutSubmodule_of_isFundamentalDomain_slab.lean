-- Prove2me | solution 1 for AutomorphicForm.exists_injOn_forall_twistedConvOp_mem_isotypicCuspSubmodule_comp_unitsMap_inf_archCutSubmodule_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e0bb9e42-250e-5346-9237-4a33e9e7e66f

import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_injOn_forall_twistedConvOp_mem_isotypicCuspSubmodule_comp_unitsMap_inf_archCutSubmodule_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped NumberField.PlaceTransport Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace R4PermSigma

section ArchCut

variable (F : Type) [Field F] [NumberField F]

theorem rightConv_mem_archCutSubmodule (tys : ArchTypeFamily F)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (hαc : Continuous α) (hαsupp : HasCompactSupport α)
    (hαt : IsArchBiFinite F tys α) :
    rightConv F g α ∈ archCutSubmodule F tys := by
  classical
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ

  set αv : AdelicGL2 (𝓞 F) F → ℂ := fun x => α x⁻¹ with hαv
  have hαvc : Continuous αv := hαc.comp continuous_inv
  have hαvsupp : HasCompactSupport αv := hαsupp.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))

  set Λ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun h x => ∫ y, g (x * y) * h y⁻¹ ∂μ with hΛ
  have hΛα : rightConv F g α = Λ αv := by
    funext x; simp only [hΛ, hαv, rightConv_apply, inv_inv, hμ]
  have hint : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, Continuous h → HasCompactSupport h →
      ∀ x, Integrable (fun y => g (x * y) * h y⁻¹) μ := fun h hh hhs x =>
    ((hg.comp (continuous_const.mul continuous_id)).mul (hh.comp continuous_inv)).integrable_of_hasCompactSupport
      (hhs.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))).mul_left
  have hΛadd : ∀ h₁ h₂ : AdelicGL2 (𝓞 F) F → ℂ, Continuous h₁ → HasCompactSupport h₁ → Continuous h₂ →
      HasCompactSupport h₂ → Λ (h₁ + h₂) = Λ h₁ + Λ h₂ := by
    intro h₁ h₂ c₁ s₁ c₂ s₂
    funext x
    simp only [hΛ, Pi.add_apply]
    rw [← integral_add (hint h₁ c₁ s₁ x) (hint h₂ c₂ s₂ x)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛsmul : ∀ (c : ℂ) (h : AdelicGL2 (𝓞 F) F → ℂ), Λ (c • h) = c • Λ h := by
    intro c h
    funext x
    simp only [hΛ, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛeq : ∀ (h : AdelicGL2 (𝓞 F) F → ℂ) (k x : AdelicGL2 (𝓞 F) F),
      Λ (fun y => h (y * k)) x = Λ h (x * k) := by
    intro h k x
    simp only [hΛ]
    have h1 := integral_mul_left_eq_self (μ := μ) (fun y => g (x * k * y) * h y⁻¹) k⁻¹
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show g (x * y) * h (y⁻¹ * k) = g (x * k * (k⁻¹ * y)) * h (k⁻¹ * y)⁻¹
    rw [mul_inv_rev, inv_inv, mul_assoc x k, mul_inv_cancel_left]

  rw [mem_archCutSubmodule_iff]
  intro w
  set ι : ↥(rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F := rowIsometryInclAt₀ F w with hιdef
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    have h1 := congrArg (fun x => archComponent F w (glArch (𝓞 F) F x)) h
    simpa only [hιdef, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply,
      glArch_adelicArchGLIncl, archComponent_archGLIncl_self] using h1
  have hcut := (mem_archCutSubmodule_iff F tys αv).mp hαt.1 w
  have hcut' : αv ∈ Submodule.span ℂ (⋃ i : Fin (tys.card w),
      {φ : AdelicGL2 (𝓞 F) F → ℂ | ∃ T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
        IsRightEquivariant ι (tys.rep w i).ρ T ∧ φ ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hcut
  obtain ⟨n, c, gen, hsum⟩ := Submodule.mem_span_set'.mp hcut'
  have hgen : ∀ j : Fin n, ∃ (i : Fin (tys.card w))
      (T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) (v : Fin (tys.rep w i).n → ℂ),
      IsRightEquivariant ι (tys.rep w i).ρ T ∧ T v = (gen j : AdelicGL2 (𝓞 F) F → ℂ) := by
    intro j
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (gen j).2
    obtain ⟨T, hT, v, hv⟩ := hi
    exact ⟨i, T, v, hT, hv⟩
  choose idx Tj vj hTj hTv using hgen

  let W : Type := (j : Fin n) → (Fin (tys.rep w (idx j)).n → ℂ)
  let ρW : Representation ℂ ↥(rowIsometrySubgroup₀ w.Completion) W :=
    { toFun := fun k => LinearMap.pi fun j => ((tys.rep w (idx j)).ρ k).comp (LinearMap.proj j)
      map_one' := by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ 1 (a j) = a j
        rw [map_one]; rfl
      map_mul' := fun k k' => by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ (k * k') (a j) = (tys.rep w (idx j)).ρ k ((tys.rep w (idx j)).ρ k' (a j))
        rw [map_mul]; rfl }
  have ρW_apply : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W) (j : Fin n),
      ρW k a j = (tys.rep w (idx j)).ρ k (a j) := fun _ _ _ => rfl
  let TW : W →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := ∑ j, (Tj j).comp (LinearMap.proj j)
  have TW_apply : ∀ a : W, TW a = ∑ j, Tj j (a j) := fun a => by
    simp only [TW, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rfl
  have hTW : IsRightEquivariant ι ρW TW := by
    intro k a x
    rw [TW_apply, TW_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ρW_apply]
    exact hTj j k (a j) x

  let Rk : ↥(rowIsometrySubgroup₀ w.Completion) → (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    fun k => LinearMap.funLeft ℂ ℂ fun y : AdelicGL2 (𝓞 F) F => y * ι k
  let V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    Submodule.span ℂ (Set.range fun k : ↥(rowIsometrySubgroup₀ w.Completion) => Rk k αv)
  have h0supp : HasCompactSupport (0 : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [HasCompactSupport, tsupport, Function.support_zero, closure_empty]; exact isCompact_empty
  have hVcc : ∀ h ∈ V, Continuous h ∧ HasCompactSupport h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨k, rfl⟩ := hh
      exact ⟨hαvc.comp (continuous_id.mul continuous_const),
        hαvsupp.comp_homeomorph (Homeomorph.mulRight (ι k))⟩
    | zero => exact ⟨continuous_const, h0supp⟩
    | add h₁ h₂ _ _ ih₁ ih₂ => exact ⟨ih₁.1.add ih₂.1, ih₁.2.add ih₂.2⟩
    | smul a h _ ih => exact ⟨ih.1.const_smul a, ih.2.smul_left (f := fun _ => a)⟩
  have hVstab : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)), ∀ h ∈ V, Rk k h ∈ V := by
    intro k h hh
    have hle : V.map (Rk k) ≤ V := by
      refine (Submodule.map_span_le _ _ _).mpr ?_
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext y
      show αv (y * ι (k * k')) = αv (y * ι k * ι k')
      rw [map_mul, mul_assoc]
    exact hle ⟨h, hh, rfl⟩

  let A : Submodule ℂ W := V.comap TW
  have hTWρ : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), TW (ρW k a) = Rk k (TW a) :=
    fun k a => funext fun x => hTW k a x
  have hA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), a ∈ A → ρW k a ∈ A := fun k a ha => by
    show TW (ρW k a) ∈ V
    rw [hTWρ]
    exact hVstab k _ ha
  let TA : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun a => Λ (TW a)
      map_add' := fun a b => by
        rw [Submodule.coe_add, map_add]
        exact hΛadd _ _ (hVcc _ a.2).1 (hVcc _ a.2).2 (hVcc _ b.2).1 (hVcc _ b.2).2
      map_smul' := fun a x => by
        rw [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact hΛsmul a _ }
  have hTA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : ↥A) (x : AdelicGL2 (𝓞 F) F),
      TA ⟨ρW k a, hA k a a.2⟩ x = TA a (x * ι k) := by
    intro k a x
    show Λ (TW (ρW k a)) x = Λ (TW a) (x * ι k)
    rw [hTWρ]
    exact hΛeq (TW a) (ι k) x
  obtain ⟨Text, hText, hTextA⟩ :=
    AutomorphicForm.exists_isRightEquivariant_comp_subtype_eq_of_injective ι hι ρW A hA TA hTA

  let a₀ : W := fun j => c j • vj j
  have hTWa₀ : TW a₀ = αv := by
    rw [TW_apply, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Tj j (c j • vj j) = c j • (gen j : AdelicGL2 (𝓞 F) F → ℂ)
    rw [map_smul, hTv]
  have ha₀ : a₀ ∈ A := by
    show TW a₀ ∈ V
    rw [hTWa₀]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y
    show αv (y * ι 1) = αv y
    rw [map_one, mul_one]
  have hgoal : rightConv F g α = Text a₀ := by
    rw [hΛα, ← hTWa₀]
    have h := congrArg (fun f : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) => f ⟨a₀, ha₀⟩) hTextA
    exact h.symm
  rw [hgoal, show a₀ = ∑ j, Pi.single j (a₀ j) from (Finset.univ_sum_single a₀).symm, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hTj' : IsRightEquivariant ι (tys.rep w (idx j)).ρ
      (Text.comp (LinearMap.single ℂ (fun j => Fin (tys.rep w (idx j)).n → ℂ) j)) := by
    intro k u x
    show Text (Pi.single j ((tys.rep w (idx j)).ρ k u)) x = Text (Pi.single j u) (x * ι k)
    rw [← hText k (Pi.single j u) x]
    have hsingle : ρW k (Pi.single j u) = Pi.single j ((tys.rep w (idx j)).ρ k u) := by
      funext j'
      rw [ρW_apply]
      by_cases hj : j' = j
      · subst hj; simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne hj, map_zero]
    rw [hsingle]
  exact Submodule.mem_iSup_of_mem (idx j) (mem_typeSubmodule_of_isRightEquivariant hTj' (a₀ j))

end ArchCut

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum.under (𝓞 K) (σ • w) = HeightOneSpectrum.under (𝓞 K) w := by
  refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 L) a = algebraMap (𝓞 K) (𝓞 L) a := by
    refine RingOfIntegers.ext ?_
    show σ⁻¹ (algebraMap K L (a : K)) = algebraMap K L (a : K)
    exact (σ⁻¹).commutes _
  rw [this]

theorem smul_dvd_of_dvd_comap (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (h : w.asIdeal ∣ N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L)) :
    (σ • w).asIdeal ∣ N := by
  rw [Ideal.dvd_iff_le] at h ⊢
  intro x hx
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  apply h
  rw [Ideal.mem_comap]
  show σ • (σ⁻¹ • x) ∈ N
  rwa [smul_inv_smul]

theorem b_eq_of_isotypicCuspSubmodule_ne_bot
    (W : Set (AdelicGL2 (𝓞 L) L)) (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L))
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : isotypicCuspSubmodule L (productionPinsOf L W U gen (adelicBox L)) ξ N S Ψ ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ S) :
    Ψ.b w = HeckeEigensystem.cNorm w *
      ((ξ ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by

  obtain ⟨φ, hφ, hφ0⟩ : ∃ φ, IsIsotypicCuspFormAt L (productionPinsOf L W U gen (adelicBox L)) ξ N S Ψ φ ∧ φ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΨ (Submodule.span_eq_bot.2 fun φ hφ => h φ hφ)
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)

  have h1 : φ (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (gen w)) * g) =
      (HeckeEigensystem.cNorm w)⁻¹ * Ψ.b w * φ g := hφ.central_eigen w hw g
  obtain ⟨hl, -⟩ := (lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξ W φ).1 hφ.smoothCusp.1.1
  have h2 := hl.central_transform ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ g
  change φ (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (gen w)) * g) = _ at h2
  rw [h1] at h2
  have h3 : (HeckeEigensystem.cNorm w)⁻¹ * Ψ.b w =
      ((ξ ⟨Matrix.GeneralLinearGroup.det (gen w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := mul_right_cancel₀ hg h2
  rw [← h3, ← mul_assoc, mul_inv_cancel₀ (HeckeEigensystem.cNorm_ne_zero w), one_mul]

theorem exists_smul_eq_of_notMem (σ : L ≃ₐ[K] L) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ SL) : ∃ w₀ ∉ SL, σ • w₀ = w := by
  refine ⟨σ⁻¹ • w, fun h => hw ?_, smul_inv_smul σ w⟩
  have hu : HeightOneSpectrum.under (𝓞 K) (σ⁻¹ • w) = HeightOneSpectrum.under (𝓞 K) w := by
    conv_rhs => rw [← smul_inv_smul σ w]
    exact (under_smul σ (σ⁻¹ • w)).symm
  exact (hSL _ _ hu).1 h

end Places

end R4PermSigma

end

open R4PermSigma in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L) :
    ∃ T : HeckeEigensystem L ℂ → HeckeEigensystem L ℂ,
      (∀ Ψ : HeckeEigensystem L ℂ, (T Ψ).level = Ψ.level ∧
        (∀ w ∈ SL, (T Ψ).a w = 0 ∧ (T Ψ).b w = 0) ∧ (∀ w ∉ SL, (T Ψ).a w = Ψ.a (σ • w))) ∧
      Set.InjOn T (cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL) ∧
      ∀ Ψ : HeckeEigensystem L ℂ, Ψ.level = N →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ ⊓ archCutSubmodule L tysL,
        twistedConvOp K L D σ φ u ∈ isotypicCuspSubmodule L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L))
            (ξL.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
              ((Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
                  AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp Subgroup.topEquiv.toMonoidHom)))
            N SL (T Ψ) ⊓ archCutSubmodule L tysL := by
  classical
  set pins := productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L) with hpins

  let bσ : HeightOneSpectrum (𝓞 L) → ℂ := fun w => HeckeEigensystem.cNorm w *
    ((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)
      (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)

  let T : HeckeEigensystem L ℂ → HeckeEigensystem L ℂ := fun Ψ =>
    ⟨Ψ.level, Ψ.level_ne_bot, fun w => if w ∈ SL then 0 else Ψ.a (σ • w), fun w => if w ∈ SL then 0 else bσ w⟩
  have Ta : ∀ Ψ w, (T Ψ).a w = if w ∈ SL then 0 else Ψ.a (σ • w) := fun _ _ => rfl
  have Tb : ∀ Ψ w, (T Ψ).b w = if w ∈ SL then 0 else bσ w := fun _ _ => rfl
  refine ⟨T, fun Ψ => ⟨rfl, fun w hw => ⟨if_pos hw, if_pos hw⟩, fun w hw => if_neg hw⟩, ?_, ?_⟩
  ·

    intro Ψ₁ hΨ₁ Ψ₂ hΨ₂ hT
    have hlev : Ψ₁.level = Ψ₂.level := hΨ₁.1.trans hΨ₂.1.symm
    have ha : Ψ₁.a = Ψ₂.a := by
      funext w
      by_cases hw : w ∈ SL
      · rw [(hΨ₁.2.1 w hw).1, (hΨ₂.2.1 w hw).1]
      · obtain ⟨w₀, hw₀, rfl⟩ := exists_smul_eq_of_notMem σ SL hSL w hw
        have h := congrArg (fun Φ : HeckeEigensystem L ℂ => Φ.a w₀) hT
        simp only [Ta, if_neg hw₀] at h
        exact h
    have hb : Ψ₁.b = Ψ₂.b := by
      funext w
      by_cases hw : w ∈ SL
      · rw [(hΨ₁.2.1 w hw).2, (hΨ₂.2.1 w hw).2]
      · rw [b_eq_of_isotypicCuspSubmodule_ne_bot ΦL _ _ ξL N SL Ψ₁ hΨ₁.2.2 w hw,
          b_eq_of_isotypicCuspSubmodule_ne_bot ΦL _ _ ξL N SL Ψ₂ hΨ₂.2.2 w hw]
    obtain ⟨l₁, hl₁, a₁, b₁⟩ := Ψ₁
    obtain ⟨l₂, hl₂, a₂, b₂⟩ := Ψ₂
    cases hlev; cases ha; cases hb
    rfl

  intro Ψ hΨN φ hφ hφc hbi hfin u hu
  obtain ⟨huV, -⟩ := Submodule.mem_inf.mp hu
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    by_cases h0 : u = 0
    · subst h0
      have hzero : twistedConvOp K L D σ φ (0 : AdelicGL2 (𝓞 L) L → ℂ) = 0 := by
        funext g
        rw [twistedConvOp_apply, rightConv_apply]
        simp [sigmaSectionActOn]
      rw [hzero]
      exact Submodule.zero_mem _

    have hiso : IsIsotypicCuspFormAt L pins ξL N SL Ψ u :=
      AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L ΦL
        (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w)
        ξL N SL Ψ u huV h0

    have htw := AutomorphicForm.isIsotypicCuspFormAt_sigmaSectionActOn_comp_unitsMap_of_isFundamentalDomain_slab
      K L D σ α β ΦL hΦs hΦ ξL SL hSL N Ψ u hiso

    have hN₁ : ∀ w : HeightOneSpectrum (𝓞 L),
        w.asIdeal ∣ N.comap (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L →+* 𝓞 L) →
          w ∈ SL := by
      intro w hw
      have h1 : σ • w ∈ SL := hN _ (smul_dvd_of_dvd_comap σ N w hw)
      exact (hSL (σ • w) w (under_smul σ w)).1 h1

    have hrc := AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_of_isFundamentalDomain_slab
      L α β ΦL hΦs hΦ _ SL _ N hN₁ hN _ φ hφ hφc hbi (sigmaSectionActOn K L D σ u) htw

    have hΨ' : IsIsotypicCuspFormAt L pins
        (ξL.comp (Subgroup.topEquiv.symm.toMonoidHom.comp
          ((Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
              AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L)).comp Subgroup.topEquiv.toMonoidHom)))
        N SL (T Ψ) (twistedConvOp K L D σ φ u) := by
      rw [twistedConvOp_apply]
      refine ⟨hrc.smoothCusp, hrc.continuous, hrc.level_invariant, fun v hv => ?_, fun v hv g => ?_⟩
      · rw [Ta, if_neg hv]
        exact hrc.hecke_eigen v hv
      · have hb : (T Ψ).toRawCentral.b v = (HeckeEigensystem.cNorm v)⁻¹ * bσ v := by
          show (HeckeEigensystem.cNorm v)⁻¹ * (if v ∈ SL then 0 else bσ v) = _
          rw [if_neg hv]
        rw [hb]
        exact hrc.central_eigen v hv g
    exact hΨ'.mem_isotypicCuspSubmodule
  ·
    rw [twistedConvOp_apply]
    have hcont : Continuous (sigmaSectionActOn K L D σ u) :=
      (continuous_of_mem_isotypicCuspSubmodule huV).comp (continuous_sigmaAdelicAct K L D σ)
    exact rightConv_mem_archCutSubmodule L tysL _ hcont φ hφ hφc hfin

end S_AutomorphicForm_exists_injOn_forall_twistedConvOp_mem_isotypicCuspSubmodule_comp_unitsMap_inf_archCutSubmodule_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_injOn_forall_twistedConvOp_mem_isotypicCuspSubmodule_comp_unitsMap_inf_archCutSubmodule_of_isFundamentalDomain_slab (solution)
