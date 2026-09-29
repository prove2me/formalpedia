-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/edb90ce9-dffd-56eb-b10e-770056599846

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass"
p2m_attr_erase "instance" "SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open NumberField AutomorphicForm
open scoped Pointwise

noncomputable section

namespace R1S80OrbProper

section Galois

variable {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
  {σ : F ≃ₐ[E] F}

theorem orderOf_eq_finrank (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank E F := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

theorem pow_finrank_eq_one (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ) :
    σ ^ Module.finrank E F = 1 := by
  rw [← orderOf_eq_finrank hgen, pow_orderOf_eq_one]

theorem prod_algEquiv_eq_prod_range (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    {M : Type*} [CommMonoid M] (f : (F ≃ₐ[E] F) → M) :
    ∏ τ : F ≃ₐ[E] F, f τ = ∏ i ∈ Finset.range (Module.finrank E F), f (σ ^ i) := by
  classical
  have horder := orderOf_eq_finrank hgen
  have hinj : Function.Injective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  have hbij : Function.Bijective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [Fintype.card_fin, horder, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  rw [← Fintype.prod_bijective _ hbij (fun i => f (σ ^ (i : ℕ))) f (fun _ => rfl),
    ← horder, ← Fin.prod_univ_eq_prod_range]

theorem prod_range_iterate_eq_algebraMap_norm (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    (a : F) :
    ∏ i ∈ Finset.range (Module.finrank E F), (⇑σ)^[i] a = algebraMap E F (Algebra.norm E a) := by
  rw [Algebra.norm_eq_prod_automorphisms, prod_algEquiv_eq_prod_range hgen]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [AlgEquiv.coe_pow]

end Galois

section Descent

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def θ : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L := fun s => (D.act σ : RingAut (AdeleRing (𝓞 L) L)) s

theorem θ_apply (s : AdeleRing (𝓞 L) L) : θ D σ s = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) s := rfl

theorem θ_mul (s t : AdeleRing (𝓞 L) L) : θ D σ (s * t) = θ D σ s * θ D σ t := map_mul _ s t
theorem θ_add (s t : AdeleRing (𝓞 L) L) : θ D σ (s + t) = θ D σ s + θ D σ t := map_add _ s t
theorem θ_sub (s t : AdeleRing (𝓞 L) L) : θ D σ (s - t) = θ D σ s - θ D σ t := map_sub _ s t
theorem θ_one : θ D σ 1 = 1 := map_one _
theorem θ_zero : θ D σ 0 = 0 := map_zero _

theorem θ_algebraMap (x : L) :
    θ D σ (algebraMap L (AdeleRing (𝓞 L) L) x) = algebraMap L (AdeleRing (𝓞 L) L) (σ x) := D.compat σ x

theorem continuous_θ : Continuous (θ D σ) := D.continuous_act σ

theorem coe_unitsAct (z : (AdeleRing (𝓞 L) L)ˣ) : ((D.unitsAct σ z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = θ D σ z := rfl

theorem coe_unitsAct_inv (z : (AdeleRing (𝓞 L) L)ˣ) :
    (((D.unitsAct σ z)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = θ D σ ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
  rw [← map_inv]; rfl

theorem continuous_unitsAct : Continuous (D.unitsAct σ : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) :=
  Continuous.units_map _ (D.continuous_act σ)

theorem act_pow_apply (k : ℕ) (s : AdeleRing (𝓞 L) L) :
    (D.act (σ ^ k) : RingAut (AdeleRing (𝓞 L) L)) s = (θ D σ)^[k] s := by
  induction k generalizing s with
  | zero =>
      rw [pow_zero, map_one, Function.iterate_zero, id_eq]
      rfl
  | succ k ih =>
      rw [pow_succ, map_mul, Function.iterate_succ_apply]
      change (D.act (σ ^ k) : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) s) = _
      rw [ih]
      rfl

theorem iterate_θ_mul (k : ℕ) (s t : AdeleRing (𝓞 L) L) :
    (θ D σ)^[k] (s * t) = (θ D σ)^[k] s * (θ D σ)^[k] t := by
  rw [← act_pow_apply, ← act_pow_apply, ← act_pow_apply, map_mul]

theorem iterate_θ_one (k : ℕ) : (θ D σ)^[k] 1 = 1 := by
  rw [← act_pow_apply, map_one]

theorem iterate_θ_prod (k : ℕ) {ι' : Type*} (s : Finset ι') (f : ι' → AdeleRing (𝓞 L) L) :
    (θ D σ)^[k] (∏ i ∈ s, f i) = ∏ i ∈ s, (θ D σ)^[k] (f i) := by
  rw [← act_pow_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => act_pow_apply D σ k (f i)

theorem iterate_θ_algebraMap (x : L) (k : ℕ) :
    (θ D σ)^[k] (algebraMap L (AdeleRing (𝓞 L) L) x) = algebraMap L (AdeleRing (𝓞 L) L) ((⇑σ)^[k] x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, θ_algebraMap, Function.iterate_succ_apply']

theorem iterate_θ_finrank [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (s : AdeleRing (𝓞 L) L) :
    (θ D σ)^[Module.finrank K L] s = s := by
  rw [← act_pow_apply, pow_finrank_eq_one hgen, map_one]
  rfl

def mcoef (lam : AdeleRing (𝓞 L) L) (k : ℕ) : AdeleRing (𝓞 L) L :=
  ∏ j ∈ Finset.range k, (θ D σ)^[j] lam

def scoef (lam w : AdeleRing (𝓞 L) L) : ℕ → AdeleRing (𝓞 L) L
  | 0 => 0
  | k + 1 => θ D σ (mcoef D σ lam k) * w + θ D σ (scoef lam w k)

theorem mcoef_zero (lam : AdeleRing (𝓞 L) L) : mcoef D σ lam 0 = 1 := by
  simp [mcoef]

theorem mcoef_succ (lam : AdeleRing (𝓞 L) L) (k : ℕ) :
    mcoef D σ lam (k + 1) = θ D σ (mcoef D σ lam k) * lam := by
  unfold mcoef
  rw [Finset.prod_range_succ', Function.iterate_zero, id_eq, θ_apply, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Function.iterate_succ_apply']
  rfl

theorem mcoef_mul (a b : AdeleRing (𝓞 L) L) (k : ℕ) :
    mcoef D σ (a * b) k = mcoef D σ a k * mcoef D σ b k := by
  unfold mcoef
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => iterate_θ_mul D σ j a b

theorem mcoef_one (k : ℕ) : mcoef D σ 1 k = 1 := by
  unfold mcoef
  exact Finset.prod_eq_one fun j _ => iterate_θ_one D σ j

theorem iterate_eq_of_θ_eq {lam w x : AdeleRing (𝓞 L) L} (h : θ D σ x = lam * x + w) (k : ℕ) :
    (θ D σ)^[k] x = mcoef D σ lam k * x + scoef D σ lam w k := by
  induction k with
  | zero => simp [mcoef_zero, scoef]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, θ_add, θ_mul, h, mcoef_succ]
      simp only [scoef]
      ring

theorem continuous_mcoef (k : ℕ) : Continuous fun lam : AdeleRing (𝓞 L) L => mcoef D σ lam k := by
  unfold mcoef
  exact continuous_finsetProd _ fun j _ => (continuous_θ D σ).iterate j

theorem continuous_scoef (k : ℕ) :
    Continuous fun p : AdeleRing (𝓞 L) L × AdeleRing (𝓞 L) L => scoef D σ p.1 p.2 k := by
  induction k with
  | zero => simpa [scoef] using continuous_const
  | succ k ih =>
      simp only [scoef]
      exact (((continuous_θ D σ).comp ((continuous_mcoef D σ k).comp continuous_fst)).mul
        continuous_snd).add ((continuous_θ D σ).comp ih)

variable [FiniteDimensional K L] [IsGalois K L]

theorem mcoef_cob (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (g : (AdeleRing (𝓞 L) L)ˣ) :
    mcoef D σ (θ D σ g * ((g⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (Module.finrank K L) = 1 := by
  set n := Module.finrank K L with hn
  have hshift : mcoef D σ (θ D σ g) n = mcoef D σ g n := by
    have h1 : mcoef D σ (g : AdeleRing (𝓞 L) L) (n + 1) = mcoef D σ (θ D σ g) n * g := by
      unfold mcoef
      rw [Finset.prod_range_succ']
      rfl
    have h2 : mcoef D σ (g : AdeleRing (𝓞 L) L) (n + 1) = mcoef D σ g n * g := by
      unfold mcoef
      rw [Finset.prod_range_succ, iterate_θ_finrank D σ hgen]
    have h3 : mcoef D σ (θ D σ g) n * g = mcoef D σ g n * g := h1.symm.trans h2
    exact Units.mul_left_inj g |>.1 h3
  rw [mcoef_mul, hshift, ← mcoef_mul, Units.mul_inv, mcoef_one]

theorem mcoef_algebraMap (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (c : L) :
    mcoef D σ (algebraMap L (AdeleRing (𝓞 L) L) c) (Module.finrank K L) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L (Algebra.norm K c)) := by
  unfold mcoef
  simp_rw [iterate_θ_algebraMap]
  rw [← map_prod, prod_range_iterate_eq_algebraMap_norm hgen]

end Descent

section GL2

variable {A : Type*} [CommRing A]

def diag2 (p q : Aˣ) : GL (Fin 2) A where
  val := !![(p : A), 0; 0, (q : A)]
  inv := !![((p⁻¹ : Aˣ) : A), 0; 0, ((q⁻¹ : Aˣ) : A)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diag2_val (p q : Aˣ) : ((diag2 p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(p : A), 0; 0, (q : A)] := rfl

theorem diag2_inv (p q : Aˣ) : (diag2 p q)⁻¹ = diag2 p⁻¹ q⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Units.ext
  rw [Units.val_mul, diag2_val, diag2_val, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diag2_mul_diag2 (p q p' q' : Aˣ) : diag2 p q * diag2 p' q' = diag2 (p * p') (q * q') := by
  apply Units.ext
  rw [Units.val_mul, diag2_val, diag2_val, diag2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diag2_val_one_zero (p q : Aˣ) : ((diag2 p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
  simp

theorem diag2_val_zero_one (p q : Aˣ) : ((diag2 p q : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
  simp

theorem scalar_eq_diag2 (z : Aˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) z = diag2 z z := by
  apply Units.ext
  rw [diag2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem val_unipotent_inv_mul_diag2_mul_unipotent (u v : A) (e₁ e₂ : Aˣ) :
    (((unipotentGL2 u)⁻¹ * diag2 e₁ e₂ * unipotentGL2 v : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![(e₁ : A), (e₁ : A) * v - (e₂ : A) * u; 0, (e₂ : A)] := by
  have hinv : (((unipotentGL2 u)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![1, -u; 0, 1] := rfl
  rw [Units.val_mul, Units.val_mul, hinv, diag2_val, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem val_inv_unipotent_inv_mul_diag2_mul_unipotent (u v : A) (e₁ e₂ : Aˣ) :
    ((((unipotentGL2 u)⁻¹ * diag2 e₁ e₂ * unipotentGL2 v)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 =
        ((e₁⁻¹ : Aˣ) : A) ∧
      ((((unipotentGL2 u)⁻¹ * diag2 e₁ e₂ * unipotentGL2 v)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 =
        ((e₂⁻¹ : Aˣ) : A) := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, diag2_inv]
  have hinv : (((unipotentGL2 v)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![1, -v; 0, 1] := rfl
  rw [Units.val_mul, Units.val_mul, hinv, diag2_val, unipotentGL2_coe]
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable [TopologicalSpace A] [IsTopologicalRing A]

omit [CommRing A] [IsTopologicalRing A] in
theorem continuous_matrix_two {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) A}
    (h00 : Continuous fun x => f x 0 0) (h01 : Continuous fun x => f x 0 1)
    (h10 : Continuous fun x => f x 1 0) (h11 : Continuous fun x => f x 1 1) : Continuous f := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem continuous_diag2_one : Continuous fun c : Aˣ => (diag2 c 1 : GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun c : Aˣ => !![(c : A), 0; 0, ((1 : Aˣ) : A)]
    exact continuous_matrix_two (by simpa using Units.continuous_val) (by simpa using continuous_const)
      (by simpa using continuous_const) (by simpa using continuous_const)
  · show Continuous fun c : Aˣ => !![((c⁻¹ : Aˣ) : A), 0; 0, (((1 : Aˣ)⁻¹ : Aˣ) : A)]
    exact continuous_matrix_two (by simpa using Units.continuous_coe_inv) (by simpa using continuous_const)
      (by simpa using continuous_const) (by simpa using continuous_const)

theorem continuous_unipotentGL2' : Continuous fun x : A => (unipotentGL2 x : GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : A => !![(1 : A), x; 0, 1]
    exact continuous_matrix_two (by simpa using continuous_const) (by simp; exact continuous_id)
      (by simpa using continuous_const) (by simpa using continuous_const)
  · show Continuous fun x : A => !![(1 : A), -x; 0, 1]
    exact continuous_matrix_two (by simpa using continuous_const) (by simpa using continuous_neg)
      (by simpa using continuous_const) (by simpa using continuous_const)

theorem continuous_val_apply (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_val_inv_apply (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j :=
  Units.continuous_coe_inv.matrix_elem i j

end GL2

section Adelic

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      θ D σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := rfl

theorem sigmaAdelicAct_unipotentGL2 (u : AdeleRing (𝓞 L) L) :
    sigmaAdelicAct K L D σ (unipotentGL2 u) = unipotentGL2 (θ D σ u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaAdelicAct_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [θ_zero, θ_one]

theorem sigmaAdelicAct_diag2 (p q : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (diag2 p q) = diag2 (D.unitsAct σ p) (D.unitsAct σ q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaAdelicAct_apply, diag2_val, diag2_val]
  fin_cases i <;> fin_cases j <;> simp [θ_zero, coe_unitsAct]

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  unfold centralScalar
  rw [scalar_eq_diag2, scalar_eq_diag2, sigmaAdelicAct_diag2]

theorem centralScalar_eq_diag2 (z : (AdeleRing (𝓞 L) L)ˣ) : centralScalar (𝓞 L) L z = diag2 z z :=
  scalar_eq_diag2 z

def prinUnit {a : L} (ha : a ≠ 0) : (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom (Units.mk0 a ha)

@[scoped simp] theorem coe_prinUnit {a : L} (ha : a ≠ 0) :
    ((prinUnit ha : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = algebraMap L (AdeleRing (𝓞 L) L) a := rfl

theorem coe_prinUnit_inv {a : L} (ha : a ≠ 0) :
    (((prinUnit ha)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = algebraMap L (AdeleRing (𝓞 L) L) a⁻¹ := by
  rw [prinUnit, ← map_inv, Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0]
  rfl

theorem globalPoints_eq_diag2 (δ₀ : GL (Fin 2) L)
    (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (h0 : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0) (h1 : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0) :
    globalPoints (𝓞 L) L δ₀ = diag2 (prinUnit h0) (prinUnit h1) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change algebraMap L (AdeleRing (𝓞 L) L) ((δ₀ : Matrix (Fin 2) (Fin 2) L) i j) = _
  rw [diag2_val]
  fin_cases i <;> fin_cases j <;> simp [hδ₀u, hδ₀l]

omit [NumberField L] in
theorem det_ne_zero_entries (δ₀ : GL (Fin 2) L)
    (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (δ₀ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det δ₀).ne_zero
  rw [Matrix.det_fin_two, hδ₀u, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem borel_eq_diag2_mul_unipotent (b : AdelicGL2 (𝓞 L) L) (hb : b ∈ adelicBorel (𝓞 L) L) :
    b = diag2 (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L))) *
      unipotentGL2 ((((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) *
        (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 := hb
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, diag2_val, unipotentGL2_coe]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      zero_mul, add_zero]
    exact (Units.mul_inv_cancel_left _ _).symm
  · simp [Matrix.mul_apply, Fin.sum_univ_two, hb10]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

end Adelic

section Main

scoped macro "mul_abel" : tactic =>
  `(tactic| (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_one]; abel))

theorem properness
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hH : ∀ h : AutomorphicForm.AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C)

    (iwasawa : ∀ g : AdelicGL2 (𝓞 L) L, ∃ b k : AdelicGL2 (𝓞 L) L,
      b ∈ adelicBorel (𝓞 L) L ∧
      NumberField.AdelicLevel.glFin (𝓞 L) L k ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L ∧
      (∀ w : InfinitePlace L, WindowedSiegel.IsRowIsometry
        (NumberField.AdelicLevel.archComponent L w (NumberField.AdelicLevel.glArch (𝓞 L) L k))) ∧
      g = b * k)
    (gl1cob : ∀ Ω : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact Ω →
      ∃ Cc : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact Cc ∧
        ∀ e : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ e * e⁻¹ ∈ Ω →
          ∃ f c : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ f = f ∧ c ∈ Cc ∧ e = f * c) :
    ∃ C' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact C' ∧
      ∀ (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
        y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y) ∈ C →
          ∃ h k : AutomorphicForm.AdelicGL2 (𝓞 L) L, h ∈ H ∧ k ∈ C' ∧ y = h * k := by
  classical
  haveI : FiniteDimensional K L := Module.IsNoetherian.finite K L

  set n : ℕ := Module.finrank K L with hn
  set σA : AdelicGL2 (𝓞 L) L →* AdelicGL2 (𝓞 L) L := sigmaAdelicAct K L D σ with hσA
  set θu : (AdeleRing (𝓞 L) L)ˣ ≃* (AdeleRing (𝓞 L) L)ˣ := D.unitsAct σ with hθu
  set gp : GL (Fin 2) L →* AdelicGL2 (𝓞 L) L := globalPoints (𝓞 L) L with hgp
  set cs : (AdeleRing (𝓞 L) L)ˣ →* AdelicGL2 (𝓞 L) L := centralScalar (𝓞 L) L with hcs

  obtain ⟨hd0, hd1⟩ := det_ne_zero_entries δ₀ hδ₀u
  set d1u : (AdeleRing (𝓞 L) L)ˣ := prinUnit hd0 with hd1u
  set d2u : (AdeleRing (𝓞 L) L)ˣ := prinUnit hd1 with hd2u
  have hgpδ : gp δ₀ = diag2 d1u d2u := globalPoints_eq_diag2 δ₀ hδ₀u hδ₀l hd0 hd1
  set ν' : K := Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0) with hν'
  have hν'ne : ν' ≠ 1 := by
    intro h1
    apply hreg
    have hmul : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) * ν' = 1 := by
      rw [hν', ← map_mul, div_mul_div_comm, mul_comm ((δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1),
        div_self (mul_ne_zero hd0 hd1), map_one]
    rwa [h1, mul_one] at hmul
  have hεne : (1 : L) - algebraMap K L ν' ≠ 0 := by
    rw [sub_ne_zero, ne_comm, ← (algebraMap K L).map_one, Ne, (algebraMap K L).injective.eq_iff]
    exact hν'ne
  set εu : (AdeleRing (𝓞 L) L)ˣ := prinUnit hεne with hεu

  set Kset : Set (AdelicGL2 (𝓞 L) L) := (adelicMaximalCompact L : Set (AdelicGL2 (𝓞 L) L)) with hKset
  have hKc : IsCompact Kset := isCompact_adelicMaximalCompact L
  set C₁ : Set (AdelicGL2 (𝓞 L) L) := Kset * C * (σA '' Kset)⁻¹ with hC₁
  have hC₁c : IsCompact C₁ := (hKc.mul hC).mul (hKc.image (continuous_sigmaAdelicAct K L D σ)).inv

  set v : Fin 2 → Fin 2 → AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L :=
    fun i j g => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j with hv
  set vi : Fin 2 → Fin 2 → AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L :=
    fun i j g => ((g⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j with hvi
  have hvc : ∀ i j, Continuous (v i j) := fun i j => continuous_val_apply i j
  have hvic : ∀ i j, Continuous (vi i j) := fun i j => continuous_val_inv_apply i j
  set E : Fin 2 → Set (AdeleRing (𝓞 L) L)ˣ := fun i =>
    (Units.embedProduct (AdeleRing (𝓞 L) L)) ⁻¹' ((v i i '' C₁) ×ˢ (MulOpposite.op '' (vi i i '' C₁))) with hE
  have hEc : ∀ i, IsCompact (E i) := fun i =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hC₁c.image (hvc i i)).prod ((hC₁c.image (hvic i i)).image MulOpposite.continuous_op))
  have hEmem : ∀ i, ∀ g ∈ C₁, ∀ e : (AdeleRing (𝓞 L) L)ˣ,
      (e : AdeleRing (𝓞 L) L) = v i i g → ((e⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = vi i i g →
        e ∈ E i := by
    intro i g hg e h1 h2
    refine ⟨⟨g, hg, h1.symm⟩, ⟨vi i i g, ⟨g, hg, rfl⟩, ?_⟩⟩
    simp [Units.embedProduct_apply, h2]
  set W : Set (AdeleRing (𝓞 L) L) := v 0 1 '' C₁ with hW
  have hWc : IsCompact W := hC₁c.image (hvc 0 1)
  set Λu : Set (AdeleRing (𝓞 L) L)ˣ := E 1 * (E 0)⁻¹ with hΛu
  have hΛuc : IsCompact Λu := (hEc 1).mul (hEc 0).inv
  set Ω : Set (AdeleRing (𝓞 L) L)ˣ := (fun l => d2u * d1u⁻¹ * l⁻¹) '' Λu with hΩ
  have hΩc : IsCompact Ω := hΛuc.image ((continuous_const.mul continuous_inv))
  obtain ⟨Cc, hCcc, hcob⟩ := gl1cob Ω hΩc
  set Λ' : Set (AdeleRing (𝓞 L) L) := (fun l : (AdeleRing (𝓞 L) L)ˣ => (l : AdeleRing (𝓞 L) L)) '' Λu with hΛ'
  have hΛ'c : IsCompact Λ' := hΛuc.image Units.continuous_val
  set W' : Set (AdeleRing (𝓞 L) L) :=
    (fun p : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L => ((p.1⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * p.2) ''
      (E 0 ×ˢ W) with hW'
  have hW'c : IsCompact W' :=
    ((hEc 0).prod hWc).image ((Units.continuous_coe_inv.comp continuous_fst).mul continuous_snd)
  set X : Set (AdeleRing (𝓞 L) L) :=
    (fun p : AdeleRing (𝓞 L) L × AdeleRing (𝓞 L) L =>
      ((εu⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * scoef D σ p.1 p.2 n) '' (Λ' ×ˢ W') with hX
  have hXc : IsCompact X := (hΛ'c.prod hW'c).image (continuous_const.mul (continuous_scoef D σ n))
  set C' : Set (AdelicGL2 (𝓞 L) L) :=
    (fun c : (AdeleRing (𝓞 L) L)ˣ => (diag2 c 1 : AdelicGL2 (𝓞 L) L)) '' Cc *
      ((fun x : AdeleRing (𝓞 L) L => (unipotentGL2 x : AdelicGL2 (𝓞 L) L)) '' X) * Kset with hC'
  have hC'c : IsCompact C' :=
    ((hCcc.image continuous_diag2_one).mul (hXc.image continuous_unipotentGL2')).mul hKc
  refine ⟨C', hC'c, fun y z hyz => ?_⟩

  obtain ⟨b, k, hb, hkf, hka, hyk⟩ := iwasawa y
  have hk : k ∈ Kset := (mem_adelicMaximalCompact_iff).2 ⟨hkf, hka⟩
  set p : (AdeleRing (𝓞 L) L)ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)) with hp
  set q : (AdeleRing (𝓞 L) L)ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 L) L)) with hq
  set x : AdeleRing (𝓞 L) L := ((p⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) *
    (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 with hx
  have hb' : b = diag2 p q * unipotentGL2 x := borel_eq_diag2_mul_unipotent b hb

  set e1u : (AdeleRing (𝓞 L) L)ˣ := p⁻¹ * d1u * θu z * θu p with he1u
  set e2u : (AdeleRing (𝓞 L) L)ˣ := q⁻¹ * d2u * θu z * θu q with he2u
  have hT : (diag2 p q)⁻¹ * gp δ₀ * σA (cs z) * σA (diag2 p q) = diag2 e1u e2u := by
    rw [hgpδ, hσA, hcs, sigmaAdelicAct_centralScalar D σ, centralScalar_eq_diag2, sigmaAdelicAct_diag2 D σ,
      diag2_inv, diag2_mul_diag2, diag2_mul_diag2, diag2_mul_diag2]
  set Pb : AdelicGL2 (𝓞 L) L := (unipotentGL2 x)⁻¹ * diag2 e1u e2u * unipotentGL2 (θ D σ x) with hPb
  have hconj : y⁻¹ * gp δ₀ * σA (cs z * y) = k⁻¹ * Pb * σA k := by
    rw [hyk, hb', map_mul, map_mul, map_mul, hσA, sigmaAdelicAct_unipotentGL2 D σ, ← hσA, hPb, ← hT,
      mul_inv_rev, mul_inv_rev]
    simp only [mul_assoc]
  have hPbC₁ : Pb ∈ C₁ := by
    have hPb' : Pb = k * (y⁻¹ * gp δ₀ * σA (cs z * y)) * (σA k)⁻¹ := by
      rw [hconj]; group
    rw [hPb']
    exact Set.mul_mem_mul (Set.mul_mem_mul hk hyz) (Set.inv_mem_inv.2 ⟨k, hk, rfl⟩)

  have hPbval := val_unipotent_inv_mul_diag2_mul_unipotent x (θ D σ x) e1u e2u
  obtain ⟨hPbi00, hPbi11⟩ := val_inv_unipotent_inv_mul_diag2_mul_unipotent x (θ D σ x) e1u e2u
  rw [← hPb] at hPbval hPbi00 hPbi11
  have he1 : e1u ∈ E 0 := hEmem 0 Pb hPbC₁ e1u (by simp [hv, hPbval]) hPbi00.symm
  have he2 : e2u ∈ E 1 := hEmem 1 Pb hPbC₁ e2u (by simp [hv, hPbval]) hPbi11.symm
  set w : AdeleRing (𝓞 L) L := (e1u : AdeleRing (𝓞 L) L) * θ D σ x - (e2u : AdeleRing (𝓞 L) L) * x with hw
  have hwW : w ∈ W := ⟨Pb, hPbC₁, by simp [hv, hPbval, hw]⟩
  set lamu : (AdeleRing (𝓞 L) L)ˣ := e2u * e1u⁻¹ with hlamu
  have hlam : lamu ∈ Λu := Set.mul_mem_mul he2 (Set.inv_mem_inv.2 he1)

  set w' : AdeleRing (𝓞 L) L := ((e1u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * w with hw'def
  have hw' : w' ∈ W' := ⟨(e1u, w), ⟨he1, hwW⟩, rfl⟩
  have hxeq : θ D σ x = (lamu : AdeleRing (𝓞 L) L) * x + w' := by
    have h1 : ((e1u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * e1u = 1 := Units.inv_mul e1u
    rw [hw'def, hw, hlamu, Units.val_mul]
    linear_combination (-(θ D σ x)) * h1
  have hiter := iterate_eq_of_θ_eq D σ hxeq n
  rw [iterate_θ_finrank D σ hgen] at hiter
  set g : (AdeleRing (𝓞 L) L)ˣ := q * p⁻¹ with hg
  have hlam_eq : lamu = d2u * d1u⁻¹ * (θu g * g⁻¹) := by
    simp only [hlamu, he1u, he2u, hg, map_mul, map_inv, mul_inv_rev, inv_inv]
    mul_abel
  have hm : mcoef D σ (lamu : AdeleRing (𝓞 L) L) n =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L ν') := by
    rw [hlam_eq, Units.val_mul, Units.val_mul (θu g), mcoef_mul, hθu, coe_unitsAct, mcoef_cob D σ hgen g,
      mul_one, Units.val_mul, mcoef_mul, hd2u, coe_prinUnit, mcoef_algebraMap D σ hgen, hd1u, coe_prinUnit_inv,
      mcoef_algebraMap D σ hgen, ← map_mul (algebraMap L (AdeleRing (𝓞 L) L)), ← map_mul (algebraMap K L),
      ← map_mul (Algebra.norm K), ← div_eq_mul_inv]
  have hxX : x ∈ X := by
    refine ⟨((lamu : AdeleRing (𝓞 L) L), w'), ⟨⟨lamu, hlam, rfl⟩, hw'⟩, ?_⟩
    show ((εu⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * scoef D σ (lamu : AdeleRing (𝓞 L) L) w' n = x
    rw [Units.inv_mul_eq_iff_eq_mul, hεu, coe_prinUnit, map_sub, map_one]
    rw [hm] at hiter
    linear_combination (-1 : AdeleRing (𝓞 L) L) * hiter

  set f : (AdeleRing (𝓞 L) L)ˣ := p * q⁻¹ with hf
  have hfΩ : θu f * f⁻¹ ∈ Ω := by
    refine ⟨lamu, hlam, ?_⟩
    rw [hlam_eq, hf, hg]
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    mul_abel
  obtain ⟨f₀, c₀, hf₀, hc₀, hfeq⟩ := hcob f hfΩ

  refine ⟨diag2 (q * f₀) q, diag2 c₀ 1 * unipotentGL2 x * k, ?_, ?_, ?_⟩
  · rw [hH]
    refine ⟨diag2_val_one_zero _ _, diag2_val_zero_one _ _, ?_⟩
    have hcen : sigmaAdelicAct K L D σ (diag2 (q * f₀) q) * (diag2 (q * f₀) q)⁻¹ =
        cs (θu q * q⁻¹) := by
      rw [sigmaAdelicAct_diag2 D σ, diag2_inv, diag2_mul_diag2, hcs, centralScalar_eq_diag2, ← hθu, map_mul, hf₀]
      congr 1
      rw [mul_inv_rev]
      mul_abel
    rw [hcen, hcs]
    unfold centralScalar
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  · exact Set.mul_mem_mul (Set.mul_mem_mul ⟨c₀, hc₀, rfl⟩ ⟨x, hxX, rfl⟩) hk
  · rw [hyk, hb', ← mul_assoc, ← mul_assoc, diag2_mul_diag2, mul_one]
    have hpq : p = q * f₀ * c₀ := by
      have : p * q⁻¹ = f₀ * c₀ := hfeq
      calc p = p * q⁻¹ * q := by group
        _ = f₀ * c₀ * q := by rw [this]
        _ = q * f₀ * c₀ := by mul_abel
    rw [← hpq]

end Main

end R1S80OrbProper
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal.R1S80OrbProper"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hH : ∀ h : AutomorphicForm.AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C) :
    ∃ C' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact C' ∧
      ∀ (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
        y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y) ∈ C →
          ∃ h k : AutomorphicForm.AdelicGL2 (𝓞 L) L, h ∈ H ∧ k ∈ C' ∧ y = h * k :=
  R1S80OrbProper.properness K L σ hgen D H hH δ₀ hδ₀u hδ₀l hreg C hC
    (AutomorphicForm.exists_mem_adelicBorel_mul_eq L)
    (M4aHerbrand.IdeleGaloisDescent.exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
      K L σ D)

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal.R1S80OrbProper"

end S_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal (solution)
