-- Prove2me | solution 1 for AutomorphicForm.constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ba98413b-57b7-5616-88cb-03d0bdc8e1e1

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_adelicHeight_sigmaAdelicAct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ENNReal NNReal

noncomputable section

namespace R4KitTruncation

section Additive

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

omit [NumberField K] in
theorem act_inv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act τ : RingAut (AdeleRing (𝓞 L) L)) x) = x := by
  calc (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act τ : RingAut (AdeleRing (𝓞 L) L)) x)
        = (D.act τ⁻¹ * D.act τ : RingAut (AdeleRing (𝓞 L) L)) x := rfl
    _ = x := by rw [← map_mul, inv_mul_cancel, map_one]; rfl

omit [NumberField K] in
theorem act_apply_inv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    (D.act τ : RingAut (AdeleRing (𝓞 L) L)) ((D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) x) = x := by
  have h := act_inv_apply D τ⁻¹ x
  rwa [inv_inv] at h

def actHomeo (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ AdeleRing (𝓞 L) L where
  toFun := (D.act τ : RingAut (AdeleRing (𝓞 L) L))
  invFun := (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L))
  left_inv := act_inv_apply D τ
  right_inv := act_apply_inv D τ
  continuous_toFun := D.continuous_act τ
  continuous_invFun := D.continuous_act τ⁻¹

omit [NumberField K] in
theorem coe_actHomeo (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    (actHomeo D τ : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act τ : RingAut (AdeleRing (𝓞 L) L)) := rfl

theorem regular_adelicAddHaar : (adelicAddHaar (𝓞 L) L).Regular := by
  dsimp only [adelicAddHaar, Measure.addHaar]
  infer_instance

attribute [local instance] regular_adelicAddHaar

omit [NumberField K] in

theorem map_act_eq_smul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    ∃ c : ℝ≥0, Measure.map (D.act τ : RingAut (AdeleRing (𝓞 L) L)) (adelicAddHaar (𝓞 L) L) =
      c • adelicAddHaar (𝓞 L) L := by
  set ν := adelicAddHaar (𝓞 L) L with hν
  let e : AdeleRing (𝓞 L) L ≃+ AdeleRing (𝓞 L) L := (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toAddEquiv
  have he : Continuous e := D.continuous_act τ
  have hsymm : (e.symm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) =
      (D.act τ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
    funext x
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    exact (act_apply_inv D τ x).symm
  have he' : Continuous e.symm := by
    rw [hsymm]; exact D.continuous_act τ⁻¹
  haveI : (Measure.map e ν).IsAddHaarMeasure := e.isAddHaarMeasure_map ν he he'
  haveI : (Measure.map e ν).Regular := Measure.Regular.map (actHomeo D τ)
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.map e ν) ν⟩

theorem measurePreserving_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) :
    MeasurePreserving (D.act τ : RingAut (AdeleRing (𝓞 L) L)) (adelicAddHaar (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  set ν := adelicAddHaar (𝓞 L) L with hν
  have hmeas : ∀ ρ : L ≃ₐ[K] L, Measurable (D.act ρ : RingAut (AdeleRing (𝓞 L) L)) :=
    fun ρ => (D.continuous_act ρ).measurable
  obtain ⟨c, h1'⟩ := map_act_eq_smul D τ
  have h1 : Measure.map (D.act τ : RingAut (AdeleRing (𝓞 L) L)) ν = (c : ℝ≥0∞) • ν := h1'

  have hk : ∀ k : ℕ, Measure.map (D.act (τ ^ k) : RingAut (AdeleRing (𝓞 L) L)) ν = (c : ℝ≥0∞) ^ k • ν := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, one_smul, map_one]
      exact Measure.map_id
    | succ k ih =>
      have hcomp : ((D.act (τ ^ (k + 1)) : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) =
          (D.act τ : RingAut (AdeleRing (𝓞 L) L)) ∘ (D.act (τ ^ k) : RingAut (AdeleRing (𝓞 L) L)) := by
        rw [pow_succ', map_mul]; rfl
      rw [hcomp, ← Measure.map_map (hmeas τ) (hmeas _), ih, Measure.map_smul, h1, smul_smul,
        pow_succ]

  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨n, hn, hτn⟩ : ∃ n : ℕ, 0 < n ∧ τ ^ n = 1 := ⟨orderOf τ, orderOf_pos τ, pow_orderOf_eq_one τ⟩
  have hνn : ν = (c : ℝ≥0∞) ^ n • ν := by
    have h := hk n
    rw [hτn, map_one] at h
    rw [← h]
    exact Measure.map_id.symm

  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : ν s ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior ν ⟨0, mem_interior_iff_mem_nhds.mpr hs_mem⟩).ne'
  have hstop : ν s ≠ ∞ := hs_compact.measure_lt_top.ne
  have hcn : c ^ n = 1 := by
    have h := congrArg (fun m : Measure (AdeleRing (𝓞 L) L) => m s) hνn
    simp only [Measure.smul_apply, smul_eq_mul] at h
    have h' : ((c : ℝ≥0∞) ^ n) = 1 := ((ENNReal.mul_left_inj hs0 hstop).1 ((one_mul _).trans h)).symm
    exact_mod_cast h'
  have hc1 : c = 1 := (pow_left_inj₀ (zero_le (a := c)) zero_le_one hn.ne').1 (by rwa [one_pow])
  refine ⟨hmeas τ, ?_⟩
  rw [h1, hc1, ENNReal.coe_one, one_smul]

omit [NumberField K] in

theorem sigmaAdelicAct_unipotentGL2 (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (q : AdeleRing (𝓞 L) L) :
    sigmaAdelicAct K L D σ (unipotentGL2 q) = unipotentGL2 ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) q) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((unipotentGL2 q : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] [Algebra K L] in

theorem unipotentGL2_algebraMap (k : L) :
    unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) = globalPoints (𝓞 L) L (unipotentGL2 k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (!![(1 : AdeleRing (𝓞 L) L), algebraMap L (AdeleRing (𝓞 L) L) k; 0, 1]) i j =
    algebraMap L (AdeleRing (𝓞 L) L) ((!![(1 : L), k; 0, 1]) i j)
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] [Algebra K L] in
theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 L) L) := by
  haveI := countable_numberField (L := L)
  refine Function.Surjective.countable (f := fun k : L => (⟨algebraMap L (AdeleRing (𝓞 L) L) k, k, rfl⟩ :
    AdeleRing.principalSubgroup (𝓞 L) L)) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

scoped instance vaddInvariantMeasure_principal :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 L) L) (AdeleRing (𝓞 L) L) (adelicAddHaar (𝓞 L) L) := by
  refine ⟨fun a s hs => ?_⟩
  obtain ⟨a, ha⟩ := a
  exact measure_preimage_add (adelicAddHaar (𝓞 L) L) a s

theorem isAddFundamentalDomain_image_adelicBox (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L)
      (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) '' adelicBox L)
      (adelicAddHaar (𝓞 L) L) := by
  have hmem : ∀ (τ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L), a ∈ AdeleRing.principalSubgroup (𝓞 L) L →
      (D.act τ : RingAut (AdeleRing (𝓞 L) L)) a ∈ AdeleRing.principalSubgroup (𝓞 L) L := by
    rintro τ _ ⟨k, rfl⟩
    exact ⟨τ k, (D.compat τ k).symm⟩
  let e : AdeleRing.principalSubgroup (𝓞 L) L ≃ AdeleRing.principalSubgroup (𝓞 L) L :=
    { toFun := fun a => ⟨(D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) a, hmem σ⁻¹ a a.2⟩
      invFun := fun a => ⟨(D.act σ : RingAut (AdeleRing (𝓞 L) L)) a, hmem σ a a.2⟩
      left_inv := fun a => Subtype.ext (act_apply_inv D σ a)
      right_inv := fun a => Subtype.ext (act_inv_apply D σ a) }
  refine (isAddFundamentalDomain_adelicBox_adelicAddHaar L).image_of_equiv (actHomeo D σ).toEquiv
    (measurePreserving_act D σ⁻¹).quasiMeasurePreserving e fun a x => ?_
  show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) (a : AdeleRing (𝓞 L) L) + x) =
    (a : AdeleRing (𝓞 L) L) + (D.act σ : RingAut (AdeleRing (𝓞 L) L)) x
  rw [map_add, act_apply_inv]

theorem constantTerm_twist (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hul : ∀ (k : L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L (unipotentGL2 k) * x) = u x)
    (g : AdelicGL2 (𝓞 L) L) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2
        (sigmaSectionActOn K L D σ u) g =
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2 u
        (sigmaAdelicAct K L D σ g) := by
  have hint : ∀ q, constantTermIntegrand unipotentGL2 (sigmaSectionActOn K L D σ u) g q =
      u (unipotentGL2 ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) q) * sigmaAdelicAct K L D σ g) := by
    intro q
    show u (sigmaAdelicAct K L D σ (unipotentGL2 q * g)) = _
    rw [map_mul, sigmaAdelicAct_unipotentGL2]
  have hint' : ∀ q, constantTermIntegrand unipotentGL2 u (sigmaAdelicAct K L D σ g) q =
      u (unipotentGL2 q * sigmaAdelicAct K L D σ g) := fun q => rfl
  unfold constantTerm
  simp_rw [hint, hint']
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure]

  congr 1

  have hemb : MeasurableEmbedding ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) :=
    (actHomeo D σ).toMeasurableEquiv.measurableEmbedding
  rw [← (measurePreserving_act D σ).setIntegral_image_emb hemb
    (fun q => u (unipotentGL2 q * sigmaAdelicAct K L D σ g)) (adelicBox L)]
  refine (isAddFundamentalDomain_image_adelicBox D σ).setIntegral_eq
    (isAddFundamentalDomain_adelicBox_adelicAddHaar L) fun a q => ?_
  obtain ⟨_, k, rfl⟩ := a
  show u (unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k + q) * sigmaAdelicAct K L D σ g) =
    u (unipotentGL2 q * sigmaAdelicAct K L D σ g)
  rw [unipotentGL2_add, unipotentGL2_algebraMap, mul_assoc, hul]

theorem lambdaT_twist (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hul : ∀ (k : L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L (unipotentGL2 k) * x) = u x)
    (T : ℝ) (g : AdelicGL2 (𝓞 L) L) :
    lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2
        (NumberField.AdelicHeight.adelicHeight L) T (sigmaSectionActOn K L D σ u) g =
      lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) unipotentGL2
        (NumberField.AdelicHeight.adelicHeight L) T u (sigmaAdelicAct K L D σ g) := by
  rw [lambdaT_apply, lambdaT_apply]
  have hH : (g ∈ highSet (NumberField.AdelicHeight.adelicHeight L) T) ↔
      (sigmaAdelicAct K L D σ g ∈ highSet (NumberField.AdelicHeight.adelicHeight L) T) := by
    rw [mem_highSet_iff, mem_highSet_iff, AutomorphicForm.adelicHeight_sigmaAdelicAct K L D σ g]
  by_cases hg : g ∈ highSet (NumberField.AdelicHeight.adelicHeight L) T
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hH.1 hg), constantTerm_twist D σ u hul g]
    rfl
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hH.2 h))]
    rfl

end Additive

end R4KitTruncation
p2m_reactivate "P2MW.S_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn.R4KitTruncation"

end
p2m_reactivate "P2MW.S_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn.R4KitTruncation"

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open R4KitTruncation in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (Dset : Set (AdelicGL2 (𝓞 L) L)) (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L))
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : ∀ (k : L) (x : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L (unipotentGL2 k) * x) = u x) :
    (∀ g : AdelicGL2 (𝓞 L) L,
      @AutomorphicForm.constantTerm _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          (sigmaSectionActOn K L D σ u) g =
        @AutomorphicForm.constantTerm _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          u (sigmaAdelicAct K L D σ g)) ∧
    ∀ (T : ℝ) (g : AdelicGL2 (𝓞 L) L),
      @AutomorphicForm.lambdaT _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T (sigmaSectionActOn K L D σ u) g =
        @AutomorphicForm.lambdaT _ (productionPinsOf L Dset U gen (adelicBox L)).nS _ _
          (productionPinsOf L Dset U gen (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) T u (sigmaAdelicAct K L D σ g) := by
  refine ⟨fun g => ?_, fun T g => ?_⟩
  · exact constantTerm_twist D σ u hu g
  · exact lambdaT_twist D σ u hu T g

end S_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn
end P2MW
export P2MW.S_AutomorphicForm_constantTerm_sigmaSectionActOn_and_lambdaT_sigmaSectionActOn (solution)
