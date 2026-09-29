-- Prove2me | solution 1 for AutomorphicForm.exists_eq_inv_mul_sigmaAdelicAct_of_prod_sigmaAdelicAct_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/eb2029c2-f343-5398-8614-76a59f8a355a

import Theorems.Thm_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_adeleRing_eqLocus_act
import Theorems.Thm_NumberField_AdeleRing_free_of_pi_linearEquiv_pi
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_inv_mul_sigmaAdelicAct_of_prod_sigmaAdelicAct_pow_eq_one
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false

noncomputable section

namespace R4H2Red

open NumberField

section FixedField

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

theorem finite_aut [NumberField L] : Finite (L ≃ₐ[K] L) := by
  let f : (L ≃ₐ[K] L) → (L ≃ₐ[ℚ] L) := fun τ => AlgEquiv.ofRingEquiv (f := (τ : L ≃+* L)) (fun q => by simp)
  have hf : Function.Injective f := by
    intro a b h
    ext x
    exact congrArg (fun e : L ≃ₐ[ℚ] L => e x) h
  exact Finite.of_injective f hf

theorem orderOf_pos_aut [NumberField L] : 0 < orderOf σ := by
  haveI := finite_aut K L
  exact orderOf_pos σ

theorem numberField_subfield [NumberField L] (E : Subfield L) : NumberField E := by
  have hf : Function.Injective ((algebraMap E L).toRatAlgHom.toLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℚ E := Module.Finite.of_injective _ hf
  exact ⟨⟩

def Efix : Subfield L := FixedPoints.subfield (Subgroup.zpowers σ) L

theorem mem_Efix_iff (x : L) : x ∈ Efix K L σ ↔ σ x = x := by
  show x ∈ MulAction.fixedPoints (Subgroup.zpowers σ) L ↔ _
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    show ((g : L ≃ₐ[K] L)) x = x
    rw [← hk]

    have hnat : ∀ j : ℕ, (σ ^ j) x = x := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
    cases k with
    | ofNat j => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hnat j
    | negSucc j =>
        rw [zpow_negSucc]
        have h1 := hnat (j + 1)
        calc (σ ^ (j + 1))⁻¹ x = (σ ^ (j + 1))⁻¹ ((σ ^ (j + 1)) x) := by rw [h1]
          _ = x := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl

theorem σ_eq_iff_mem_range (x : L) :
    σ x = x ↔ x ∈ Set.range (algebraMap (Efix K L σ) L) := by
  rw [← mem_Efix_iff]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

end FixedField

section Transport

theorem forall_free_of_ringEquiv {A R : Type} [CommRing A] [CommRing R] (e : A ≃+* R) (m n : ℕ)
    (hA : ∀ (P : Type) [AddCommGroup P] [Module A P],
      ((Fin n → P) ≃ₗ[A] (Fin (m * n) → A)) → Module.Free A P)
    (P : Type) [AddCommGroup P] [Module R P]
    (f : (Fin n → P) ≃ₗ[R] (Fin (m * n) → R)) : Module.Free R P := by

  letI instA : Module A P := Module.compHom P e.toRingHom
  have hsmul : ∀ (a : A) (p : P), (a • p : P) = (e a • p : P) := fun _ _ => rfl

  let g : (Fin n → P) ≃ₗ[A] (Fin (m * n) → A) :=
    { toFun := fun v i => e.symm (f v i)
      invFun := fun w => f.symm (fun i => e (w i))
      map_add' := by
        intro v w
        funext i
        show e.symm (f (v + w) i) = e.symm (f v i) + e.symm (f w i)
        rw [map_add, Pi.add_apply, map_add]
      map_smul' := by
        intro a v
        funext i
        show e.symm (f (a • v) i) = a * e.symm (f v i)
        have hv : (a • v : Fin n → P) = ((e a) • v : Fin n → P) := by
          funext j
          exact hsmul a (v j)
        rw [hv, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := by
        intro v
        show f.symm (fun i => e (e.symm (f v i))) = v
        have : (fun i => e (e.symm (f v i))) = f v := by
          funext i; exact e.apply_symm_apply _
        rw [this, LinearEquiv.symm_apply_apply]
      right_inv := by
        intro w
        funext i
        show e.symm (f (f.symm (fun j => e (w j))) i) = w i
        rw [LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] }
  haveI hfreeA : Module.Free A P := hA P g

  let b := Module.Free.chooseBasis A P
  let b' : Module.Basis _ R P := b.mapCoeffs e (fun c p => (hsmul c p).symm)
  exact Module.Free.of_basis b'

end Transport

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

abbrev θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L := (D.act σ : RingAut (AdeleRing (𝓞 L) L))

theorem θ_pow (k : ℕ) : (θ K L σ D) ^ k = (D.act (σ ^ k) : RingAut (AdeleRing (𝓞 L) L)) := by
  show (D.act σ) ^ k = D.act (σ ^ k)
  rw [map_pow]

theorem sigmaAdelicAct_pow_eq (k : ℕ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.sigmaAdelicAct K L D (σ ^ k) x =
      Matrix.GeneralLinearGroup.map (((θ K L σ D) ^ k : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) :
        AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L) x := by
  rw [θ_pow]
  rfl

theorem main (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hx : ((List.range (orderOf σ)).map
      fun k => AutomorphicForm.sigmaAdelicAct K L D (σ ^ k) x).prod = 1) :
    ∃ y : AutomorphicForm.AdelicGL2 (𝓞 L) L, x = y⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ y := by
  classical

  have hn : 0 < orderOf σ := orderOf_pos_aut K L σ

  let E : Subfield L := Efix K L σ
  haveI : NumberField E := numberField_subfield L E
  have hE : ∀ z : L, σ z = z ↔ z ∈ Set.range (algebraMap E L) := σ_eq_iff_mem_range K L σ

  obtain ⟨e, -⟩ := M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_adeleRing_eqLocus_act K L E σ D hE

  have hfree : ∀ (P : Type) [AddCommGroup P]
      [Module (RingHom.eqLocus (θ K L σ D).toRingHom (RingHom.id (AdeleRing (𝓞 L) L))) P],
      ((Fin (orderOf σ) → P) ≃ₗ[RingHom.eqLocus (θ K L σ D).toRingHom (RingHom.id (AdeleRing (𝓞 L) L))]
          (Fin (2 * orderOf σ) → RingHom.eqLocus (θ K L σ D).toRingHom (RingHom.id (AdeleRing (𝓞 L) L)))) →
        Module.Free (RingHom.eqLocus (θ K L σ D).toRingHom (RingHom.id (AdeleRing (𝓞 L) L))) P := by
    intro P _ _ f
    exact forall_free_of_ringEquiv e 2 (orderOf σ)
      (fun Q _ _ g => NumberField.AdeleRing.free_of_pi_linearEquiv_pi E 2 (orderOf σ) hn Q g) P f

  have hθ : ∀ l : L, θ K L σ D (algebraMap L (AdeleRing (𝓞 L) L) l) = algebraMap L (AdeleRing (𝓞 L) L) (σ l) :=
    fun l => D.compat σ l
  have hθn : (θ K L σ D) ^ orderOf σ = 1 := by
    rw [θ_pow, pow_orderOf_eq_one, map_one]

  have hx' : ((List.range (orderOf σ)).map fun k =>
      Matrix.GeneralLinearGroup.map (((θ K L σ D) ^ k : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) :
        AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L) x).prod = 1 := by
    have hfun : (fun k => Matrix.GeneralLinearGroup.map (((θ K L σ D) ^ k : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) :
        AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L) x) = fun k => AutomorphicForm.sigmaAdelicAct K L D (σ ^ k) x := by
      funext k
      exact (sigmaAdelicAct_pow_eq K L σ D k x).symm
    rw [hfun]
    exact hx

  obtain ⟨y, hy⟩ :=
    RingEquiv.exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free K L σ hn
      (AdeleRing (𝓞 L) L) (θ K L σ D) hθ hθn 2 hfree x hx'
  exact ⟨y, hy⟩

end Main

end R4H2Red

end

open NumberField in
theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hx : ((List.range (orderOf σ)).map
      fun k => AutomorphicForm.sigmaAdelicAct K L D (σ ^ k) x).prod = 1) :
    ∃ y : AutomorphicForm.AdelicGL2 (𝓞 L) L, x = y⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ y :=
  R4H2Red.main K L σ D x hx

end S_AutomorphicForm_exists_eq_inv_mul_sigmaAdelicAct_of_prod_sigmaAdelicAct_pow_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_inv_mul_sigmaAdelicAct_of_prod_sigmaAdelicAct_pow_eq_one (solution)
