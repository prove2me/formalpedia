-- Prove2me | solution 1 for AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/73bf9126-3152-5ca6-83e2-aadca8b0e81d

import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

noncomputable section

namespace R4URed

open MeasureTheory MeasureTheory.Measure NumberField Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev GG : Type := AutomorphicForm.AdelicGL2 (𝓞 L) L

abbrev θ : GG L →* GG L := AutomorphicForm.sigmaAdelicAct K L D σ

abbrev ZZ : Subgroup (GG L) := Subgroup.center (GG L)

abbrev G1 : Subgroup (GG L) :=
  MonoidHom.eqLocus ((QuotientGroup.mk' (ZZ L)).comp (θ K L D σ)) (QuotientGroup.mk' (ZZ L))

abbrev Hf : Subgroup (GG L) := MonoidHom.eqLocus (θ K L D σ) (MonoidHom.id (GG L))

theorem mem_G1_iff {g : GG L} :
    g ∈ G1 K L D σ ↔ g⁻¹ * θ K L D σ g ∈ ZZ L := by
  show (QuotientGroup.mk' _ (θ K L D σ g) = QuotientGroup.mk' _ g) ↔ _
  rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]

theorem mem_Hf_iff {g : GG L} : g ∈ Hf K L D σ ↔ θ K L D σ g = g := Iff.rfl

theorem θ_comp_inv :
    (θ K L D σ).comp (AutomorphicForm.sigmaAdelicAct K L D σ⁻¹) = MonoidHom.id _ := by
  rw [← AutomorphicForm.sigmaAdelicAct_mul, mul_inv_cancel, AutomorphicForm.sigmaAdelicAct_one]

theorem θ_surjective : Function.Surjective (θ K L D σ) := by
  intro g
  refine ⟨AutomorphicForm.sigmaAdelicAct K L D σ⁻¹ g, ?_⟩
  have h := congrArg (fun f : GG L →* GG L => f g) (θ_comp_inv K L D σ)
  exact h

theorem θ_mem_center {z : GG L} (hz : z ∈ ZZ L) : θ K L D σ z ∈ ZZ L := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := θ_surjective K L D σ g
  rw [← map_mul, ← map_mul, hz g']

theorem center_le_G1 : ZZ L ≤ G1 K L D σ := fun _ hz =>
  (mem_G1_iff K L D σ).mpr ((ZZ L).mul_mem ((ZZ L).inv_mem hz) (θ_mem_center K L D σ hz))

theorem Hf_le_G1 : Hf K L D σ ≤ G1 K L D σ := by
  intro h hh
  rw [mem_G1_iff, (mem_Hf_iff K L D σ).mp hh, inv_mul_cancel]
  exact (ZZ L).one_mem

theorem θ_eq_mul (g : GG L) :
    θ K L D σ g = g * (g⁻¹ * θ K L D σ g) := by
  rw [mul_inv_cancel_left]

theorem conj_mem_Hf {g h : GG L} (hg : g ∈ G1 K L D σ) (hh : h ∈ Hf K L D σ) :
    g * h * g⁻¹ ∈ Hf K L D σ := by
  have hz : g⁻¹ * θ K L D σ g ∈ ZZ L := (mem_G1_iff K L D σ).mp hg
  set z := g⁻¹ * θ K L D σ g with hzdef
  have hθg : θ K L D σ g = g * z := θ_eq_mul K L D σ g
  rw [mem_Hf_iff] at hh ⊢
  rw [map_mul, map_mul, map_inv, hh, hθg, mul_inv_rev]
  have hzc := Subgroup.mem_center_iff.mp hz

  calc g * z * h * (z⁻¹ * g⁻¹) = g * (h * z) * (z⁻¹ * g⁻¹) := by rw [hzc h, mul_assoc g z h]
    _ = g * h * g⁻¹ := by group

theorem isClosed_center : IsClosed (ZZ L : Set (GG L)) := by
  have h : (ZZ L : Set (GG L)) = ⋂ g : GG L, {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

theorem isClosed_G1 : IsClosed (G1 K L D σ : Set (GG L)) := by
  have h : (G1 K L D σ : Set (GG L)) =
      (fun g => g⁻¹ * θ K L D σ g) ⁻¹' (ZZ L : Set (GG L)) := by
    ext g; exact mem_G1_iff K L D σ
  rw [h]
  exact (isClosed_center L).preimage
    (continuous_id.inv.mul (AutomorphicForm.continuous_sigmaAdelicAct K L D σ))

theorem isClosed_Hf : IsClosed (Hf K L D σ : Set (GG L)) := by
  have h : (Hf K L D σ : Set (GG L)) = {g | θ K L D σ g = g} := by
    ext g; exact mem_Hf_iff K L D σ
  rw [h]
  exact isClosed_eq (AutomorphicForm.continuous_sigmaAdelicAct K L D σ) continuous_id

theorem finite_algEquiv : Finite (L ≃ₐ[K] L) := by
  haveI : CharZero K := (algebraMap K L).charZero
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  exact Finite.of_fintype (L ≃ₐ[K] L)

def nσ : ℕ := orderOf σ

theorem nσ_pos : 0 < nσ K L σ := by
  haveI := finite_algEquiv K L
  exact (isOfFinOrder_of_finite σ).orderOf_pos

abbrev θpow (k : ℕ) : GG L →* GG L := AutomorphicForm.sigmaAdelicAct K L D (σ ^ k)

theorem θpow_zero_apply (g : GG L) : θpow K L D σ 0 g = g := by
  show AutomorphicForm.sigmaAdelicAct K L D (σ ^ 0) g = g
  rw [pow_zero, AutomorphicForm.sigmaAdelicAct_one]; rfl

theorem θpow_succ_apply (k : ℕ) (g : GG L) :
    θpow K L D σ (k + 1) g = θ K L D σ (θpow K L D σ k g) := by
  show AutomorphicForm.sigmaAdelicAct K L D (σ ^ (k + 1)) g = _
  rw [pow_succ', AutomorphicForm.sigmaAdelicAct_mul]; rfl

theorem θpow_nσ_apply (g : GG L) : θpow K L D σ (nσ K L σ) g = g := by
  show AutomorphicForm.sigmaAdelicAct K L D (σ ^ orderOf σ) g = g
  rw [pow_orderOf_eq_one, AutomorphicForm.sigmaAdelicAct_one]; rfl

def θZ : ZZ L →* ZZ L :=
  ((θ K L D σ).comp (ZZ L).subtype).codRestrict (ZZ L) fun z => θ_mem_center K L D σ z.2

@[scoped simp] theorem coe_θZ (z : ZZ L) : ((θZ K L D σ z : ZZ L) : GG L) = θ K L D σ z := rfl

def orb (z : ZZ L) (k : ℕ) : ZZ L :=
  ⟨θpow K L D σ k z, by
    induction k with
    | zero => rw [θpow_zero_apply]; exact z.2
    | succ k ih => rw [θpow_succ_apply]; exact θ_mem_center K L D σ ih⟩

@[scoped simp] theorem coe_orb (z : ZZ L) (k : ℕ) : ((orb K L D σ z k : ZZ L) : GG L) = θpow K L D σ k z :=
  rfl

theorem orb_zero (z : ZZ L) : orb K L D σ z 0 = z :=
  Subtype.ext (θpow_zero_apply K L D σ z)

theorem orb_nσ (z : ZZ L) : orb K L D σ z (nσ K L σ) = z :=
  Subtype.ext (θpow_nσ_apply K L D σ z)

theorem θZ_orb (z : ZZ L) (k : ℕ) : θZ K L D σ (orb K L D σ z k) = orb K L D σ z (k + 1) :=
  Subtype.ext (by rw [coe_θZ, coe_orb, coe_orb, θpow_succ_apply])

theorem θpow_eq_mul_prod {g : GG L} (z : ZZ L) (hg : θ K L D σ g = g * z) (k : ℕ) :
    θpow K L D σ k g = g * ((∏ i ∈ Finset.range k, orb K L D σ z i : ZZ L) : GG L) := by
  induction k with
  | zero => rw [Finset.prod_range_zero, OneMemClass.coe_one, mul_one, θpow_zero_apply]
  | succ k ih =>
    rw [θpow_succ_apply, ih, map_mul, hg]
    have h1 : θ K L D σ ((∏ i ∈ Finset.range k, orb K L D σ z i : ZZ L) : GG L) =
        ((θZ K L D σ (∏ i ∈ Finset.range k, orb K L D σ z i) : ZZ L) : GG L) := rfl
    rw [h1, map_prod]
    simp_rw [θZ_orb]
    rw [Finset.prod_range_succ' (fun i => orb K L D σ z i), orb_zero, mul_assoc, ← Subgroup.coe_mul,
      mul_comm z]

theorem prod_orb_eq_one {g : GG L} (z : ZZ L) (hg : θ K L D σ g = g * z) :
    ∏ i ∈ Finset.range (nσ K L σ), orb K L D σ z i = 1 := by
  have h := θpow_eq_mul_prod K L D σ z hg (nσ K L σ)
  rw [θpow_nσ_apply] at h
  have h2 : ((∏ i ∈ Finset.range (nσ K L σ), orb K L D σ z i : ZZ L) : GG L) = 1 :=
    (mul_eq_left.mp h.symm)
  exact_mod_cast h2

def W (z : ZZ L) : ZZ L := ∏ i ∈ Finset.range (nσ K L σ), orb K L D σ z i ^ i

theorem θZ_W {g : GG L} (z : ZZ L) (hg : θ K L D σ g = g * z) :
    θZ K L D σ (W K L D σ z) = W K L D σ z * z ^ nσ K L σ := by
  set n := nσ K L σ with hn
  set a : ℕ → ZZ L := orb K L D σ z with ha
  have hN : ∏ i ∈ Finset.range n, a i = 1 := prod_orb_eq_one K L D σ z hg
  have han : a n = z := orb_nσ K L D σ z
  have ha0 : a 0 = z := orb_zero K L D σ z

  have hθW : θZ K L D σ (W K L D σ z) = ∏ i ∈ Finset.range n, a (i + 1) ^ i := by
    unfold W
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← ha, θZ_orb]

  have hQ1 : ∏ i ∈ Finset.range (n + 1), a i ^ i = (∏ i ∈ Finset.range n, a (i + 1) ^ (i + 1)) := by
    rw [Finset.prod_range_succ' (fun i => a i ^ i)]
    rw [pow_zero, mul_one]
  have hQ2 : ∏ i ∈ Finset.range (n + 1), a i ^ i = W K L D σ z * z ^ n := by
    rw [Finset.prod_range_succ (fun i => a i ^ i), han]
    rfl

  have hR : ∏ i ∈ Finset.range n, a (i + 1) = 1 := by
    have h1 : ∏ i ∈ Finset.range (n + 1), a i = (∏ i ∈ Finset.range n, a (i + 1)) * a 0 :=
      Finset.prod_range_succ' a n
    have h2 : ∏ i ∈ Finset.range (n + 1), a i = (∏ i ∈ Finset.range n, a i) * a n :=
      Finset.prod_range_succ a n
    rw [hN, one_mul, han] at h2
    rw [h2, ha0] at h1
    exact (mul_eq_right.mp h1.symm)
  have hsplit : ∏ i ∈ Finset.range n, a (i + 1) ^ (i + 1) =
      (∏ i ∈ Finset.range n, a (i + 1) ^ i) * ∏ i ∈ Finset.range n, a (i + 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ]
  rw [hθW]
  rw [← hQ2, hQ1, hsplit, hR, mul_one]

theorem pow_nσ_mem {g : GG L} (hg : g ∈ G1 K L D σ) :
    ∃ h w : GG L, h ∈ Hf K L D σ ∧ w ∈ ZZ L ∧ g ^ nσ K L σ = h * w := by
  have hz : g⁻¹ * θ K L D σ g ∈ ZZ L := (mem_G1_iff K L D σ).mp hg
  set z : ZZ L := ⟨g⁻¹ * θ K L D σ g, hz⟩ with hzdef
  have hθg : θ K L D σ g = g * z := θ_eq_mul K L D σ g
  set n := nσ K L σ with hn
  refine ⟨g ^ n * ((W K L D σ z : ZZ L) : GG L)⁻¹, W K L D σ z, ?_, (W K L D σ z).2, ?_⟩
  · rw [mem_Hf_iff, map_mul, map_inv, map_pow, hθg]
    have hW : θ K L D σ ((W K L D σ z : ZZ L) : GG L) =
        ((W K L D σ z * z ^ n : ZZ L) : GG L) := by
      rw [← θZ_W K L D σ z hθg]; rfl
    rw [hW]
    have hc : Commute g (z : GG L) := (Subgroup.mem_center_iff.mp z.2 g)
    rw [hc.mul_pow, Subgroup.coe_mul, Subgroup.coe_pow, mul_inv_rev, mul_assoc,
      mul_inv_cancel_left]
  · rw [inv_mul_cancel_right]

attribute [local instance] NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing

section Measure

theorem secondCountable_GG : SecondCountableTopology (GG L) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L

theorem secondCountable_G1 : SecondCountableTopology (G1 K L D σ) :=
  haveI := secondCountable_GG L
  TopologicalSpace.Subtype.secondCountableTopology (G1 K L D σ : Set (GG L))

theorem locallyCompactSpace_G1 : LocallyCompactSpace (G1 K L D σ) :=
  (isClosed_G1 K L D σ).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem locallyCompactSpace_Hf : LocallyCompactSpace (Hf K L D σ) :=
  (isClosed_Hf K L D σ).isClosedEmbedding_subtypeVal.locallyCompactSpace

abbrev H1 : Subgroup (G1 K L D σ) := (Hf K L D σ).subgroupOf (G1 K L D σ)

theorem mem_H1_iff {x : G1 K L D σ} : x ∈ H1 K L D σ ↔ (x : GG L) ∈ Hf K L D σ :=
  Subgroup.mem_subgroupOf

theorem isClosed_H1 : IsClosed (H1 K L D σ : Set (G1 K L D σ)) := by
  have h : (H1 K L D σ : Set (G1 K L D σ)) = Subtype.val ⁻¹' (Hf K L D σ : Set (GG L)) := by
    ext x; exact mem_H1_iff K L D σ
  rw [h]
  exact (isClosed_Hf K L D σ).preimage continuous_subtype_val

theorem locallyCompactSpace_H1 : LocallyCompactSpace (H1 K L D σ) :=
  haveI := locallyCompactSpace_G1 K L D σ
  (isClosed_H1 K L D σ).isClosedEmbedding_subtypeVal.locallyCompactSpace

def eH : H1 K L D σ →* Hf K L D σ where
  toFun x := ⟨(x : G1 K L D σ), (mem_H1_iff K L D σ).mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def eHinv : Hf K L D σ → H1 K L D σ := fun y =>
  ⟨⟨(y : GG L), Hf_le_G1 K L D σ y.2⟩, (mem_H1_iff K L D σ).mpr y.2⟩

theorem continuous_eH : Continuous (eH K L D σ) :=
  Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

theorem continuous_eHinv : Continuous (eHinv K L D σ) :=
  Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

def eHomeo : H1 K L D σ ≃ₜ Hf K L D σ where
  toFun := eH K L D σ
  invFun := eHinv K L D σ
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_eH K L D σ
  continuous_invFun := continuous_eHinv K L D σ

theorem isOpenEmbedding_eH : Topology.IsOpenEmbedding (eH K L D σ) :=
  (eHomeo K L D σ).isOpenEmbedding

variable [MeasurableSpace (GG L)] [BorelSpace (GG L)]

theorem exists_haar_rightInvariant_H1 :
    ∃ μH : Measure (H1 K L D σ), μH.IsHaarMeasure ∧ μH.IsMulRightInvariant := by
  haveI := locallyCompactSpace_Hf K L D σ
  haveI := locallyCompactSpace_H1 K L D σ
  set ν : Measure (Hf K L D σ) := Measure.haar with hν
  haveI : ν.IsHaarMeasure := by rw [hν]; exact Measure.isHaarMeasure_haarMeasure _
  haveI : ν.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id K L σ D ν
  refine ⟨ν.comap (eH K L D σ), ?_, ?_⟩
  · exact IsHaarMeasure.comap (mH := inferInstance) (f := eH K L D σ) ν (isOpenEmbedding_eH K L D σ)
  · exact IsMulRightInvariant.comap (f := eH K L D σ) ν
      (isOpenEmbedding_eH K L D σ).measurableEmbedding

theorem map_mul_right_eq_self_of_mem_Hf (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure]
    (y : G1 K L D σ) (hy : (y : GG L) ∈ Hf K L D σ) :
    Measure.map (· * y) μ₁ = μ₁ := by
  haveI := secondCountable_G1 K L D σ
  haveI := locallyCompactSpace_G1 K L D σ
  haveI := locallyCompactSpace_H1 K L D σ
  obtain ⟨μH, hμH, hμHr⟩ := exists_haar_rightInvariant_H1 K L D σ
  haveI := hμH
  haveI := hμHr
  have hHc := isClosed_H1 K L D σ

  have hconj : ∀ q : G1 K L D σ, q * y * q⁻¹ ∈ H1 K L D σ := fun q =>
    (mem_H1_iff K L D σ).mpr (by
      have := conj_mem_Hf K L D σ q.2 hy
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this)
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_mul_const y) hA]

  have hmeasA : Measurable (A.indicator (1 : G1 K L D σ → ℝ≥0∞)) := measurable_one.indicator hA
  have hmeasAy : Measurable fun g : G1 K L D σ => A.indicator (1 : G1 K L D σ → ℝ≥0∞) (g * y) :=
    hmeasA.comp (measurable_mul_const y)
  have h1 : μ₁ ((· * y) ⁻¹' A) = ∫⁻ g, A.indicator (1 : G1 K L D σ → ℝ≥0∞) (g * y) ∂μ₁ := by
    rw [← lintegral_indicator_one ((measurable_mul_const y) hA)]
    rfl
  have h2 : μ₁ A = ∫⁻ g, A.indicator (1 : G1 K L D σ → ℝ≥0∞) g ∂μ₁ :=
    (lintegral_indicator_one hA).symm
  rw [h1, h2,
    HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ₁ (H1 K L D σ) hHc μH _ hmeasAy,
    HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ₁ (H1 K L D σ) hHc μH _ hmeasA]
  refine lintegral_congr fun q => ?_

  set c : H1 K L D σ := ⟨q.out * y * q.out⁻¹, hconj q.out⟩ with hc
  have hrew : ∀ x : H1 K L D σ,
      (x : G1 K L D σ) * q.out * y = ((x * c : H1 K L D σ) : G1 K L D σ) * q.out := by
    intro x
    rw [Subgroup.coe_mul]
    show (x : G1 K L D σ) * q.out * y = (x : G1 K L D σ) * (q.out * y * q.out⁻¹) * q.out
    group
  simp_rw [hrew]
  exact lintegral_mul_right_eq_self
    (fun x : H1 K L D σ => A.indicator (1 : G1 K L D σ → ℝ≥0∞) ((x : G1 K L D σ) * q.out)) c

omit [BorelSpace (GG L)] in

theorem map_mul_right_eq_self_of_mem_center (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure]
    (z : G1 K L D σ) (hz : (z : GG L) ∈ ZZ L) :
    Measure.map (· * z) μ₁ = μ₁ := by
  have h : (fun x : G1 K L D σ => x * z) = fun x => z * x := by
    funext x
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz x)
  rw [h]
  exact map_mul_left_eq_self μ₁ z

omit [BorelSpace (GG L)] in

theorem eq_one_of_smul_eq (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure] {c : ℝ≥0}
    (h : (c • μ₁ : Measure (G1 K L D σ)) = μ₁) : c = 1 := by
  haveI := locallyCompactSpace_G1 K L D σ
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (G1 K L D σ)) := inferInstance
  have hpos : 0 < μ₁ K₀ := Measure.measure_pos_of_nonempty_interior μ₁ K₀.interior_nonempty
  have hlt : μ₁ K₀ < ∞ := K₀.isCompact.measure_lt_top
  have h1 : ((c : ℝ≥0∞) * μ₁ K₀) = 1 * μ₁ K₀ := by
    have := congrArg (fun m : Measure (G1 K L D σ) => m K₀) h
    simp only [Measure.smul_apply] at this
    rw [one_mul]
    rwa [ENNReal.smul_def, smul_eq_mul] at this
  rw [ENNReal.mul_left_inj hpos.ne' hlt.ne] at h1
  exact_mod_cast h1

theorem map_mul_right_eq_modularCharacter_smul (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure]
    (g : G1 K L D σ) :
    haveI := locallyCompactSpace_G1 K L D σ
    Measure.map (· * g) μ₁ = (Measure.modularCharacter g : ℝ≥0) • μ₁ := by
  haveI := secondCountable_G1 K L D σ
  haveI := locallyCompactSpace_G1 K L D σ
  have h1 := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ₁) μ₁
  rw [← Measure.modularCharacterFun_eq_haarScalarFactor μ₁ g] at h1
  exact h1

theorem modularCharacter_eq_one_of_map_eq (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure]
    (g : G1 K L D σ) (h : Measure.map (· * g) μ₁ = μ₁) :
    haveI := locallyCompactSpace_G1 K L D σ
    Measure.modularCharacter g = 1 := by
  haveI := locallyCompactSpace_G1 K L D σ
  have h2 := map_mul_right_eq_modularCharacter_smul K L D σ μ₁ g
  rw [h] at h2
  exact eq_one_of_smul_eq K L D σ μ₁ h2.symm

theorem modularCharacter_eq_one (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure]
    (g : G1 K L D σ) :
    haveI := locallyCompactSpace_G1 K L D σ
    Measure.modularCharacter g = 1 := by
  haveI := locallyCompactSpace_G1 K L D σ

  obtain ⟨h, w, hh, hw, hpow⟩ := pow_nσ_mem K L D σ g.2
  set h₁ : G1 K L D σ := ⟨h, Hf_le_G1 K L D σ hh⟩ with hh₁
  set w₁ : G1 K L D σ := ⟨w, center_le_G1 K L D σ hw⟩ with hw₁
  have hpow₁ : g ^ nσ K L σ = h₁ * w₁ := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact hpow)
  have hΔh : Measure.modularCharacter h₁ = 1 :=
    modularCharacter_eq_one_of_map_eq K L D σ μ₁ h₁ (map_mul_right_eq_self_of_mem_Hf K L D σ μ₁ h₁ hh)
  have hΔw : Measure.modularCharacter w₁ = 1 :=
    modularCharacter_eq_one_of_map_eq K L D σ μ₁ w₁
      (map_mul_right_eq_self_of_mem_center K L D σ μ₁ w₁ hw)
  have hΔn : Measure.modularCharacter g ^ nσ K L σ = 1 := by
    rw [← map_pow, hpow₁, map_mul, hΔh, hΔw, mul_one]
  exact (pow_eq_one_iff_of_nonneg zero_le (nσ_pos K L σ).ne').mp hΔn

theorem main (μ₁ : Measure (G1 K L D σ)) [μ₁.IsHaarMeasure] : μ₁.IsMulRightInvariant := by
  haveI := locallyCompactSpace_G1 K L D σ
  refine ⟨fun g => ?_⟩
  have h := map_mul_right_eq_modularCharacter_smul K L D σ μ₁ g
  rw [modularCharacter_eq_one K L D σ μ₁ g, one_smul] at h
  exact h

end Measure

end R4URed
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center.R4URed"

open MeasureTheory NumberField

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μH : Measure (MonoidHom.eqLocus
        ((QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L))).comp
          (AutomorphicForm.sigmaAdelicAct K L D σ))
        (QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))))
    [μH.IsHaarMeasure] : μH.IsMulRightInvariant :=
  R4URed.main K L D σ μH

end
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center.R4URed"

end S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
end P2MW
export P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center (solution)
