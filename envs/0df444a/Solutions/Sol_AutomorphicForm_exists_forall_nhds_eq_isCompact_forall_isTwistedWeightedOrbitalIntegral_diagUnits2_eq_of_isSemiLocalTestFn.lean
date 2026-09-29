-- Prove2me | solution 1 for AutomorphicForm.exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3d79126b-70ba-5a5a-ae65-a9d737b7d6cc

import Mathlib
import Theorems.Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_nhds_nhds_forall_apply_inv_mul_diagUnits2_mul_toTensorGL_diagUnits2_mul_sigmaGL_eq_of_isSemiLocalTestFn
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.gl2Weyl_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace S6bRoots

open AutomorphicForm

theorem scalar_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  simp only [Units.val_mul, h]
  exact (Matrix.scalar_commute (c : R) (fun r' => mul_comm _ _) _).eq

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) z) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem pow_apply_zero_zero_of_diag {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (h01 : M 0 1 = 0) (h10 : M 1 0 = 0) (n : ℕ) :
    (M ^ n) 0 0 = (M 0 0) ^ n ∧ (M ^ n) 0 1 = 0 ∧ (M ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h00, h01', h10'⟩ := ih
    rw [pow_succ, pow_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two, h00, h10, mul_zero, add_zero]
    · rw [Matrix.mul_apply, Fin.sum_univ_two, h01, h01', mul_zero, zero_mul, add_zero]
    · rw [Matrix.mul_apply, Fin.sum_univ_two, h10', h10, zero_mul, mul_zero, add_zero]

def diagSubalgebra (R : Type*) [CommRing R] : Subalgebra R (Matrix (Fin 2) (Fin 2) R) where
  carrier := {M | M 0 1 = 0 ∧ M 1 0 = 0}
  mul_mem' := by
    rintro A B ⟨hA01, hA10⟩ ⟨hB01, hB10⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two, hA01, hB01, mul_zero, zero_mul, add_zero]
    · rw [Matrix.mul_apply, Fin.sum_univ_two, hA10, hB10, zero_mul, mul_zero, add_zero]
  add_mem' := by
    rintro A B ⟨hA01, hA10⟩ ⟨hB01, hB10⟩
    exact ⟨by rw [Matrix.add_apply, hA01, hB01, add_zero], by rw [Matrix.add_apply, hA10, hB10, add_zero]⟩
  algebraMap_mem' := by
    intro r
    refine ⟨?_, ?_⟩ <;> simp [Matrix.algebraMap_matrix_apply]

theorem integral_map_subgroupCast {G : Type*} [Group G] [TopologicalSpace G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁)) (g : G → ℝ) :
    ∫ t : H₂, g (t : G) ∂(@Measure.map H₁ H₂ (borel H₁) (borel H₂)
        (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) =
      ∫ t : H₁, g (t : G) ∂τ := by
  subst e
  exact congrArg (fun ν => ∫ t : H₂, g (t : G) ∂ν) (@Measure.map_id H₂ (borel H₂) τ)

theorem isHaarMeasure_map_subgroupCast {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁))
    (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ) :
    @Measure.IsHaarMeasure H₂ _ _ (borel H₂) (@Measure.map H₁ H₂ (borel H₁) (borel H₂)
        (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) := by
  subst e
  exact (@Measure.map_id H₂ (borel H₂) τ).symm ▸ hτ

theorem map_subgroupCast_apply_preimage {G : Type*} [Group G] [TopologicalSpace G]
    (H₁ H₂ : Subgroup G) (e : H₂ = H₁) (τ : @Measure H₁ (borel H₁)) (S : Set G) :
    (@Measure.map H₁ H₂ (borel H₁) (borel H₂) (fun t => ⟨(t : G), e.symm ▸ t.2⟩) τ) (Subtype.val ⁻¹' S) =
      τ (Subtype.val ⁻¹' S) := by
  subst e
  exact congrArg (fun ν => ν (Subtype.val ⁻¹' S)) (@Measure.map_id H₂ (borel H₂) τ)

theorem exists_nhds_root (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) (ha : (a : v.adicCompletion K) ≠ 1) (n : ℕ) (hn : 0 < n) :
    ∀ V ∈ nhds (1 : v.adicCompletion K), ∃ W ∈ nhds (1 : v.adicCompletion K),
      ∀ ε : (v.adicCompletion K)ˣ, (ε : v.adicCompletion K) ∈ W →
        ∃ η : (v.adicCompletion K)ˣ, (η : v.adicCompletion K) ∈ V ∧ η ^ n = ε := by
  intro V hV
  set γ₀ : GL (Fin 2) (v.adicCompletion K) := diagUnits2 a 1 with hγ₀
  have hγ₀val : (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![(a : v.adicCompletion K), 0; 0, 1] := by
    rw [hγ₀, LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl
  have hreg : IsRegularSemisimple γ₀ := by
    show IsUnit _
    rw [hγ₀val, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    have : ((a : v.adicCompletion K) + 1) ^ 2 - 4 * ((a : v.adicCompletion K) * 1 - 0 * 0) =
        ((a : v.adicCompletion K) - 1) ^ 2 := by ring
    rw [this]
    exact IsUnit.pow 2 (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha))

  have hV' : {g : GL (Fin 2) (v.adicCompletion K) | (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ∈ V} ∈
      nhds (1 : GL (Fin 2) (v.adicCompletion K)) := by
    have hc : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 :=
      Units.continuous_val.matrix_elem 0 0
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨W₂, hW₂, hroot⟩ :=
    AutomorphicForm.exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple K v γ₀ hreg 1 n hn _ hV'

  have hsc : Continuous fun ε : (v.adicCompletion K)ˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) ε : GL (Fin 2) (v.adicCompletion K)) := by
    rw [Units.continuous_iff]
    constructor
    · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr fun ε => ?_
      rfl
    · refine ((continuous_pi fun _ : Fin 2 => (Units.continuous_coe_inv : Continuous fun u : (v.adicCompletion K)ˣ => ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))).matrix_diagonal).congr fun ε => ?_
      show Matrix.diagonal (fun _ : Fin 2 => ((ε⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
        (((Matrix.GeneralLinearGroup.scalar (Fin 2) ε)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      rw [← map_inv]
      rfl
  have hW₁ : (fun ε : (v.adicCompletion K)ˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) ε) ⁻¹' W₂ ∈
      nhds (1 : (v.adicCompletion K)ˣ) :=
    hsc.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hW₂)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hW₁
  obtain ⟨W, hW, hWsub⟩ := hW₁
  refine ⟨W, by simpa using hW, fun ε hε => ?_⟩
  have hεW : Matrix.GeneralLinearGroup.scalar (Fin 2) ε ∈ W₂ := hWsub hε
  have hcent : Matrix.GeneralLinearGroup.scalar (Fin 2) ε ∈ localCentralizer K v γ₀ := by
    rw [Subgroup.mem_centralizer_iff]
    rintro g rfl
    exact (scalar_comm ε γ₀).symm
  obtain ⟨β, hβV, hβadj, hβpow⟩ := hroot _ hεW hcent
  rw [map_one, inv_one, one_mul] at hβpow

  have hβdiag : (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈ diagSubalgebra (v.adicCompletion K) := by
    refine (Algebra.adjoin_le ?_) hβadj
    rintro M rfl
    refine ⟨?_, ?_⟩
    · rw [hγ₀val]; rfl
    · rw [hγ₀val]; rfl
  obtain ⟨hβ01, hβ10⟩ := hβdiag
  obtain ⟨hpow00, -, -⟩ := pow_apply_zero_zero_of_diag _ hβ01 hβ10 n
  have hβu : IsUnit ((β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) := by
    have hdet : IsUnit (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := Matrix.isUnits_det_units β
    rw [Matrix.det_fin_two, hβ01, hβ10, mul_zero, sub_zero] at hdet
    exact (IsUnit.mul_iff.mp hdet).1
  refine ⟨hβu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]; exact hβV
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← hpow00, ← Units.val_pow_eq_pow_val, hβpow]
    rfl

end S6bRoots

namespace TwWindow

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

def P (a t : (v.adicCompletion K)ˣ) (J : ℂ) : Prop :=
  ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
    AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) ∧
    ∃ τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' ∧
      τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 ∧
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J

noncomputable def iotaU : (v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight :
    v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom)

section r2dropins

theorem coe_iotaU (d : (v.adicCompletion K)ˣ) :
    ((iotaU K L v d : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) = Algebra.TensorProduct.includeRight (R := K) (A := L) (d : v.adicCompletion K) := rfl

theorem toTensorGL_diagUnits2_iotaU (a b : (v.adicCompletion K)ˣ) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) = diagUnits2 (iotaU K L v a) (iotaU K L v b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      coe_iotaU]

theorem diagUnits2_mul' (x y x' y' : (L ⊗[K] v.adicCompletion K)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_mul_toTensorGL_diagUnits2 (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (d₁ d₂ : (v.adicCompletion K)ˣ) :
    diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d₁ d₂) =
      diagUnits2 (α * iotaU K L v d₁) (β * iotaU K L v d₂) := by
  rw [toTensorGL_diagUnits2_iotaU, diagUnits2_mul']

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ (diagUnits2 x y) =
      diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) x)
        (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    (AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] x)
        ((Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] v.adicCompletion K)ˣ) :
    AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 x y) =
      diagUnits2 (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] x).prod)
        (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K))^[i] y).prod) := by
  unfold AutomorphicForm.normString
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul']

theorem sigmaU_iotaU (d : (v.adicCompletion K)ˣ) :
    Units.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ : L ⊗[K] v.adicCompletion K →* L ⊗[K] v.adicCompletion K) (iotaU K L v d) = iotaU K L v d := by
  apply Units.ext
  rw [Units.coe_map, coe_iotaU]
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (v.adicCompletion K)) ((1 : L) ⊗ₜ (d : v.adicCompletion K)) = (1 : L) ⊗ₜ (d : v.adicCompletion K)
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem prod_iterate_mul_fixed (f : (L ⊗[K] v.adicCompletion K)ˣ →* (L ⊗[K] v.adicCompletion K)ˣ) (x c : (L ⊗[K] v.adicCompletion K)ˣ) (hc : f c = c) (n : ℕ) :
    ((List.range n).map fun i => (⇑f)^[i] (x * c)).prod = ((List.range n).map fun i => (⇑f)^[i] x).prod * c ^ n := by
  have hit : ∀ i, (⇑f)^[i] (x * c) = (⇑f)^[i] x * c := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, hc]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, ih, hit, pow_succ]
    simp only [mul_assoc, mul_left_comm ((⇑f)^[n] x) (c ^ n) c, mul_comm ((⇑f)^[n] x) (c ^ n)]

theorem diagUnits2_inj {x y x' y' : (L ⊗[K] v.adicCompletion K)ˣ} (h : diagUnits2 x y = diagUnits2 x' y') : x = x' ∧ y = y' := by
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp at h00 h11
  exact ⟨Units.ext h00, Units.ext h11⟩

theorem normString_diagUnits2_mul_iotaU [FiniteDimensional K L]
    (α β : (L ⊗[K] v.adicCompletion K)ˣ) (a b d₁ d₂ : (v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b)) :
    AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 (α * iotaU K L v d₁) (β * iotaU K L v d₂)) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K)
        (diagUnits2 (a * d₁ ^ Module.finrank K L) (b * d₂ ^ Module.finrank K L)) := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2_iotaU] at hN ⊢
  obtain ⟨h1, h2⟩ := diagUnits2_inj K L v hN
  rw [prod_iterate_mul_fixed K L v _ α _ (sigmaU_iotaU K L σ v d₁),
    prod_iterate_mul_fixed K L v _ β _ (sigmaU_iotaU K L σ v d₂), h1, h2, map_mul, map_pow, map_mul, map_pow]

theorem mem_centralizer_diagUnits2_iff (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) (v.adicCompletion K))) ↔
      ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
      ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
  have hsub : IsUnit ((a : v.adicCompletion K) - (b : v.adicCompletion K)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg
    have hcomm := hg _ (Set.mem_singleton _)
    have hM := congrArg (fun x : GL (Fin 2) (v.adicCompletion K) => ((x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) hcomm
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at hM
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    constructor
    · have : ((a : v.adicCompletion K) - (b : v.adicCompletion K)) * ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
        linear_combination e01
      exact (hsub.mul_right_eq_zero).1 this
    · have : ((a : v.adicCompletion K) - (b : v.adicCompletion K)) * ((g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
        linear_combination (-1 : v.adicCompletion K) * e10
      exact (hsub.mul_right_eq_zero).1 this
  · rintro ⟨h01, h10⟩ h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem twistedCentralizer_diagUnits2_eq [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (α β α' β' : (L ⊗[K] v.adicCompletion K)ˣ) (a b a' b' : (v.adicCompletion K)ˣ)
    (hab : a ≠ b) (hab' : a' ≠ b')
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (hN' : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α' β') =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' b')) :
    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β') := by
  have hu : IsUnit ((a : v.adicCompletion K) - (b : v.adicCompletion K)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab (Units.ext h))
  have hu' : IsUnit ((a' : v.adicCompletion K) - (b' : v.adicCompletion K)) :=
    isUnit_iff_ne_zero.2 (sub_ne_zero.2 fun h => hab' (Units.ext h))
  rw [AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub K L σ hgen (v.adicCompletion K) a b hu α β hN,
    AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub K L σ hgen (v.adicCompletion K) a' b' hu' α' β' hN']
  congr 1
  ext g
  rw [mem_centralizer_diagUnits2_iff K v a b hab, mem_centralizer_diagUnits2_iff K v a' b' hab']

end r2dropins

theorem transport_of_subgroup_eq {G : Type*} [Group G] [TopologicalSpace G]
    (S : Set G) {H₁ H₂ : Subgroup G} (h : H₁ = H₂) (τ : @Measure H₁ (borel H₁))
    (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ) :
    ∃ τ₂ : @Measure H₂ (borel H₂), @Measure.IsHaarMeasure H₂ _ _ (borel H₂) τ₂ ∧
      τ₂ {t | (t : G) ∈ S} = τ {t | (t : G) ∈ S} ∧
      ∀ f : G → ℝ, ∀ x : G,
        (@integral H₂ ℝ _ _ (borel H₂) τ₂ fun t => f ((t : G) * x)) =
          @integral H₁ ℝ _ _ (borel H₁) τ fun t => f ((t : G) * x) := by
  subst h
  exact ⟨τ, hτ, rfl, fun _ _ => rfl⟩

theorem P_shift [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (U D : Set ((v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ))
    (hUD : ∀ ab : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, ab ∈ U →
      ∀ d : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, d ∈ D →
      ∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 ab.1 ab.2) →
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d.1 d.2)) *
              AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) =
            φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x))
    (a t η : (v.adicCompletion K)ˣ) (ht : t ≠ 1) (ht' : t * η ^ Module.finrank K L ≠ 1)
    (hU : (a, a * t) ∈ U) (hD : ((1 : (v.adicCompletion K)ˣ), η) ∈ D) (J : ℂ)
    (hP : P K L σ v φ a t J) : P K L σ v φ a (t * η ^ Module.finrank K L) J := by
  obtain ⟨α, β, hN, τ', hτ', h1, hJ⟩ := hP
  have hshift : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 1 η)) *
          AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) =
        φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) :=
    fun x => hUD (a, a * t) hU (1, η) hD α β hN x
  have hL1 : diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 1 η) =
      diagUnits2 α (β * iotaU K L v η) := by
    rw [diagUnits2_mul_toTensorGL_diagUnits2, map_one, mul_one]
  have hN' : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α (β * iotaU K L v η)) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * (t * η ^ Module.finrank K L))) := by
    have h := normString_diagUnits2_mul_iotaU K L σ v α β a (a * t) 1 η hN
    rw [map_one, mul_one, one_pow, mul_one, mul_assoc] at h
    exact h
  have hat : a ≠ a * t := by
    intro h; apply ht
    exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
  have hat' : a ≠ a * (t * η ^ Module.finrank K L) := by
    intro h; apply ht'
    exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
  have hT := twistedCentralizer_diagUnits2_eq K L σ v hgen α β α (β * iotaU K L v η) a (a * t) a
    (a * (t * η ^ Module.finrank K L)) hat hat' hN hN'
  obtain ⟨τ₂, hτ₂, h1₂, hint⟩ := transport_of_subgroup_eq (AutomorphicForm.semiLocalIntegralSet K L v) hT τ' hτ'
  refine ⟨α, β * iotaU K L v η, hN', τ₂, hτ₂, by rw [h1₂]; exact h1, ?_⟩
  obtain ⟨s, ⟨hs0, hsm, hsc, hs1⟩, hJs⟩ := hJ
  refine ⟨s, ⟨hs0, hsm, hsc, fun x hx => ?_⟩, ?_⟩
  · rw [hint]
    apply hs1 x
    rw [← hL1, hshift x] at hx
    exact hx
  · rw [hJs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← hL1, hshift x]

theorem tdir [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) (a₀ t₀ : (v.adicCompletion K)ˣ) (ht₀ : t₀ ≠ 1) :
    ∃ U ∈ nhds a₀, ∃ V ∈ nhds t₀, ∀ a ∈ U, ∀ t ∈ V, ∀ J : ℂ, P K L σ v φ a t J ↔ P K L σ v φ a t₀ J := by
  classical
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hat₀ : a₀ ≠ a₀ * t₀ := by
    intro h; apply ht₀
    exact mul_left_cancel (a := a₀) (by rw [mul_one]; exact h.symm)
  obtain ⟨U, hU, D, hD, hUD⟩ :=
    AutomorphicForm.exists_nhds_nhds_forall_apply_inv_mul_diagUnits2_mul_toTensorGL_diagUnits2_mul_sigmaGL_eq_of_isSemiLocalTestFn
      K L σ v φ hφ a₀ (a₀ * t₀) hat₀

  have hD₂ : {η : (v.adicCompletion K)ˣ | ((1 : (v.adicCompletion K)ˣ), η) ∈ D} ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
    have hc : Continuous fun η : (v.adicCompletion K)ˣ => ((1 : (v.adicCompletion K)ˣ), η) :=
      continuous_const.prodMk continuous_id
    exact hc.continuousAt.preimage_mem_nhds hD
  obtain ⟨V₁, hV₁, hV₁D⟩ : ∃ V₁ ∈ nhds (1 : v.adicCompletion K),
      ∀ η : (v.adicCompletion K)ˣ, (η : v.adicCompletion K) ∈ V₁ → ((1 : (v.adicCompletion K)ˣ), η) ∈ D := by
    rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hD₂
    obtain ⟨V₁, hV₁, hsub⟩ := hD₂
    exact ⟨V₁, by simpa using hV₁, fun η hη => hsub hη⟩
  have ht₀' : ((t₀ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 1 := fun h => ht₀ (Units.val_eq_one.1 h)
  obtain ⟨W, hW, hroot⟩ := S6bRoots.exists_nhds_root K v t₀ ht₀' (Module.finrank K L) hn V₁ hV₁

  have hcU : Continuous fun p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ => (p.1, p.1 * p.2) :=
    continuous_fst.prodMk (continuous_fst.mul continuous_snd)
  obtain ⟨Ua, hUa, Vt, hVt, hUV⟩ := mem_nhds_prod_iff.1 (hcU.continuousAt.preimage_mem_nhds hU)
  have hne : {t : (v.adicCompletion K)ˣ | t ≠ 1} ∈ nhds t₀ := isOpen_ne.mem_nhds ht₀
  have hW1 : {t : (v.adicCompletion K)ˣ | (((t₀ * t⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W} ∈ nhds t₀ := by
    have hc : Continuous fun t : (v.adicCompletion K)ˣ => (((t₀ * t⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) :=
      Units.continuous_val.comp (continuous_const.mul continuous_inv)
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hW
  have hW2 : {t : (v.adicCompletion K)ˣ | (((t * t₀⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W} ∈ nhds t₀ := by
    have hc : Continuous fun t : (v.adicCompletion K)ˣ => (((t * t₀⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) :=
      Units.continuous_val.comp (continuous_id.mul continuous_const)
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hW
  refine ⟨Ua, hUa, Vt ∩ ({t | t ≠ 1} ∩ ({t | (((t₀ * t⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W} ∩
      {t | (((t * t₀⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W})),
    Filter.inter_mem hVt (Filter.inter_mem hne (Filter.inter_mem hW1 hW2)), ?_⟩
  rintro a ha t ⟨htV, htne, ht1, ht2⟩ J
  have hUat : (a, a * t) ∈ U := hUV (Set.mk_mem_prod ha htV)
  have hUat₀ : (a, a * t₀) ∈ U := hUV (Set.mk_mem_prod ha (mem_of_mem_nhds hVt))
  constructor
  · intro hP
    obtain ⟨η, hηV, hηn⟩ := hroot (t₀ * t⁻¹) ht1
    have heq : t * η ^ Module.finrank K L = t₀ := by
      rw [hηn, mul_comm t, inv_mul_cancel_right]
    have ht' : t * η ^ Module.finrank K L ≠ 1 := by rw [heq]; exact ht₀
    have key := P_shift K L σ v φ hgen U D hUD a t η htne ht' hUat (hV₁D η hηV) J hP
    rwa [heq] at key
  · intro hP
    obtain ⟨η, hηV, hηn⟩ := hroot (t * t₀⁻¹) ht2
    have heq : t₀ * η ^ Module.finrank K L = t := by
      rw [hηn, mul_comm t₀, inv_mul_cancel_right]
    have ht' : t₀ * η ^ Module.finrank K L ≠ 1 := by rw [heq]; exact htne
    have key := P_shift K L σ v φ hgen U D hUD a t₀ η ht₀ ht' hUat₀ (hV₁D η hηV) J hP
    rwa [heq] at key

end TwWindow

namespace TwWindowR2

open AutomorphicForm

section algebra
variable {R : Type*} [CommRing R]

theorem diag_eq_scalar_mul (a t : Rˣ) :
    diagUnits2 a (a * t) = Matrix.GeneralLinearGroup.scalar (Fin 2) (a * t) * diagUnits2 t⁻¹ 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem diag_offdiag (a b : Rˣ) :
    ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧
    ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem trace_sq_sub_four_det_diag (a b : Rˣ) :
    Matrix.trace ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) ^ 2 -
      4 * Matrix.det ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ((a : R) - (b : R)) ^ 2 := by
  simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

end algebra

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

theorem isUnit_sub_diag (a t : (v.adicCompletion K)ˣ) (ht : t ≠ 1) :
    IsUnit (((a : (v.adicCompletion K)ˣ) : v.adicCompletion K) - ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)) := by
  rw [Units.val_mul, ← mul_one_sub]
  refine (Units.isUnit a).mul (isUnit_iff_ne_zero.2 (sub_ne_zero.2 ?_))
  intro h
  exact ht (Units.val_eq_one.1 h.symm)

theorem isRegularSemisimple_diag (a t : (v.adicCompletion K)ˣ) (ht : t ≠ 1) :
    AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) := by
  rw [AutomorphicForm.isRegularSemisimple_iff, trace_sq_sub_four_det_diag]
  exact (isUnit_sub_diag K v a t ht).pow 2

theorem P_unique [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) {a t : (v.adicCompletion K)ˣ} (ht : t ≠ 1) {J₁ J₂ : ℂ}
    (h₁ : TwWindow.P K L σ v φ a t J₁) (h₂ : TwWindow.P K L σ v φ a t J₂) : J₁ = J₂ := by
  obtain ⟨α₁, β₁, hN₁, τ₁, hτ₁, hτ₁1, hJ₁⟩ := h₁
  obtain ⟨α₂, β₂, hN₂, τ₂, hτ₂, hτ₂1, hJ₂⟩ := h₂
  exact AutomorphicForm.eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal K L σ hgen v (diagUnits2 a (a * t))
    (isRegularSemisimple_diag K v a t ht) (diag_offdiag a (a * t)).1 (diag_offdiag a (a * t)).2
    (diagUnits2 α₁ β₁) (diagUnits2 α₂ β₂) hN₁ hN₂ τ₁ hτ₁ hτ₁1 τ₂ hτ₂ hτ₂1 φ hφ J₁ J₂ hJ₁ hJ₂

theorem P_central [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) (t : (v.adicCompletion K)ˣ) (ht : t ≠ 1) :
    ∃ W ∈ nhds (1 : v.adicCompletion K), ∀ ε : (v.adicCompletion K)ˣ, (ε : v.adicCompletion K) ∈ W → ∀ (a : (v.adicCompletion K)ˣ) (J : ℂ),
      TwWindow.P K L σ v φ a t J → TwWindow.P K L σ v φ (a * ε) t J := by
  have ht' : ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 1 := by
    intro h; exact ht (inv_eq_one.1 (Units.val_eq_one.1 h))
  obtain ⟨W, hW, hmain⟩ := AutomorphicForm.exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2 K L σ hgen v t⁻¹ ht' φ hφ
  refine ⟨W, hW, fun ε hε a J hP => ?_⟩
  obtain ⟨α, β, hN, τ', hτ', hτ'1, hJ⟩ := hP
  rw [diag_eq_scalar_mul] at hN
  obtain ⟨δ', hN', τ'', hτ'', hτ''1, hJ'⟩ := hmain ε hε (a * t) (diagUnits2 α β) hN τ' hτ' hτ'1 J hJ
  have hcl : Matrix.GeneralLinearGroup.scalar (Fin 2) (a * t * ε) * diagUnits2 t⁻¹ 1 =
      diagUnits2 (a * ε) (a * ε * t) := by
    rw [mul_right_comm a t ε, diag_eq_scalar_mul]
  rw [hcl] at hN'
  obtain ⟨α', β', rfl⟩ := AutomorphicForm.exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2 K L σ (v.adicCompletion K) (a * ε) (a * ε * t)
    (isUnit_sub_diag K v (a * ε) t ht) δ' hN'
  exact ⟨α', β', hN', τ'', hτ'', hτ''1, hJ'⟩

end TwWindowR2

namespace TwWindowR2

open AutomorphicForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

noncomputable def Φ (p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ) : ℂ :=
  haveI := Classical.propDecidable (∃ J : ℂ, TwWindow.P K L σ v φ p.1 p.2 J)
  if h : ∃ J : ℂ, TwWindow.P K L σ v φ p.1 p.2 J then Classical.choose h else 0

theorem Φ_spec_of_P {a t : (v.adicCompletion K)ˣ} {J : ℂ} (hJ : TwWindow.P K L σ v φ a t J) :
    TwWindow.P K L σ v φ a t (Φ K L σ v φ (a, t)) := by
  classical
  have h : ∃ J : ℂ, TwWindow.P K L σ v φ a t J := ⟨J, hJ⟩
  simp only [Φ, dif_pos h]
  exact Classical.choose_spec h

theorem Φ_eq_zero_of_not {a t : (v.adicCompletion K)ˣ} (h : ¬ ∃ J : ℂ, TwWindow.P K L σ v φ a t J) :
    Φ K L σ v φ (a, t) = 0 := by
  classical
  simp only [Φ, dif_neg h]

theorem Φ_congr [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) {a t a₀ t₀ : (v.adicCompletion K)ˣ} (ht₀ : t₀ ≠ 1)
    (h : ∀ J : ℂ, TwWindow.P K L σ v φ a t J ↔ TwWindow.P K L σ v φ a₀ t₀ J) :
    Φ K L σ v φ (a, t) = Φ K L σ v φ (a₀, t₀) := by
  classical
  by_cases hex : ∃ J : ℂ, TwWindow.P K L σ v φ a t J
  · obtain ⟨J, hJ⟩ := hex
    have h1 : TwWindow.P K L σ v φ a₀ t₀ (Φ K L σ v φ (a, t)) := (h _).1 (Φ_spec_of_P K L σ v φ hJ)
    have h2 : TwWindow.P K L σ v φ a₀ t₀ (Φ K L σ v φ (a₀, t₀)) := Φ_spec_of_P K L σ v φ ((h _).1 hJ)
    exact P_unique K L σ v φ hgen hφ ht₀ h1 h2
  · have hex₀ : ¬ ∃ J : ℂ, TwWindow.P K L σ v φ a₀ t₀ J := fun ⟨J, hJ⟩ => hex ⟨J, (h J).2 hJ⟩
    rw [Φ_eq_zero_of_not K L σ v φ hex, Φ_eq_zero_of_not K L σ v φ hex₀]

theorem Φ_locallyConstant [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ) (hp : p.2 ≠ 1) :
    ∃ U ∈ nhds p, ∀ q ∈ U, Φ K L σ v φ q = Φ K L σ v φ p := by
  obtain ⟨a₀, t₀⟩ := p
  change t₀ ≠ 1 at hp
  obtain ⟨U, hU, V, hV, htd⟩ := TwWindow.tdir K L σ v φ hgen hφ a₀ t₀ hp
  obtain ⟨W, hW, hcen⟩ := P_central K L σ v φ hgen hφ t₀ hp

  have hc1 : ContinuousAt (fun a : (v.adicCompletion K)ˣ => (((a₀⁻¹ * a : (v.adicCompletion K)ˣ)) : v.adicCompletion K)) a₀ :=
    (Units.continuous_val.comp (continuous_const.mul continuous_id)).continuousAt
  have hc2 : ContinuousAt (fun a : (v.adicCompletion K)ˣ => (((a⁻¹ * a₀ : (v.adicCompletion K)ˣ)) : v.adicCompletion K)) a₀ :=
    (Units.continuous_val.comp (continuous_inv.mul continuous_const)).continuousAt
  have hW1 : {a : (v.adicCompletion K)ˣ | (((a₀⁻¹ * a : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W} ∈ nhds a₀ := by
    apply hc1.preimage_mem_nhds
    simpa using hW
  have hW2 : {a : (v.adicCompletion K)ˣ | (((a⁻¹ * a₀ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W} ∈ nhds a₀ := by
    apply hc2.preimage_mem_nhds
    simpa using hW
  refine ⟨(U ∩ ({a : (v.adicCompletion K)ˣ | (((a₀⁻¹ * a : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W} ∩
      {a : (v.adicCompletion K)ˣ | (((a⁻¹ * a₀ : (v.adicCompletion K)ˣ)) : v.adicCompletion K) ∈ W})) ×ˢ V,
    prod_mem_nhds (Filter.inter_mem hU (Filter.inter_mem hW1 hW2)) hV, ?_⟩
  rintro ⟨a, t⟩ ⟨⟨haU, haW1, haW2⟩, htV⟩
  apply Φ_congr K L σ v φ hgen hφ hp
  intro J
  refine (htd a haU t htV J).trans ⟨fun h => ?_, fun h => ?_⟩
  · have := hcen (a⁻¹ * a₀) haW2 a J h
    rwa [mul_inv_cancel_left] at this
  · have := hcen (a₀⁻¹ * a) haW1 a₀ J h
    rwa [mul_inv_cancel_left] at this

end TwWindowR2

namespace TwS6a

open AutomorphicForm

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) x = sigmaTensor K L A σ (sigmaTensor K L A τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (x : L ⊗[K] A) : sigmaTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] x = sigmaTensor K L A (σ ^ n) x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

theorem sigmaGL_iterate_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = Nat.card (Subgroup.zpowers σ) :=
    IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at h1
  rw [← h1]
  exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate, pow_finrank_eq_one, sigmaTensor_one_apply]

private def _root_.TwS6a.P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

p2m_export "TwS6a" "P"
theorem P_succ (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ := by
  simp only [P, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem normString_eq_P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem iterate_sigmaGL_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] (x * y) = (⇑(sigmaGL K L A σ))^[n] x * (⇑(sigmaGL K L A σ))^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem iterate_sigmaGL_inv (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] x⁻¹ = ((⇑(sigmaGL K L A σ))^[n] x)⁻¹ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_inv]

theorem P_conj (σ : L ≃ₐ[K] L) (x δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) n = x⁻¹ * P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] x := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [P_succ, P_succ, ih, iterate_sigmaGL_mul, iterate_sigmaGL_mul, iterate_sigmaGL_inv,
      ← Function.iterate_succ_apply (⇑(sigmaGL K L A σ)) n x]
    group

theorem normString_conj [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) = x⁻¹ * normString K L A σ δ * x := by
  rw [normString_eq_P, P_conj, sigmaGL_iterate_finrank, ← normString_eq_P]

theorem continuous_P [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (n : ℕ) :
    Continuous fun δ : GL (Fin 2) (L ⊗[K] A) => P K L A σ δ n := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  have hσ : Continuous (sigmaGL K L A σ) := by
    refine Continuous.units_map _ ?_
    refine continuous_id.matrix_map ?_
    have h := IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
    exact h
  have hit : ∀ k : ℕ, Continuous fun δ : GL (Fin 2) (L ⊗[K] A) => (⇑(sigmaGL K L A σ))^[k] δ := by
    intro k
    induction k with
    | zero => exact continuous_id
    | succ k ih => simp only [Function.iterate_succ_apply']; exact hσ.comp ih
  induction n with
  | zero => simp only [P, List.range_zero, List.map_nil, List.prod_nil]; exact continuous_const
  | succ n ih => simp only [P_succ]; exact ih.mul (hit n)

end sigma

theorem isCompact_sq_preimage {F : Type*} [NormedField F] [ProperSpace F] (C : Set F) (hC : IsCompact C) :
    IsCompact {x : F | x ^ 2 ∈ C} := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  have hcl : IsClosed {x : F | x ^ 2 ∈ C} := hC.isClosed.preimage (continuous_pow 2)
  refine (isCompact_closedBall (0 : F) (Real.sqrt R)).of_isClosed_subset hcl fun x hx => ?_
  have h := hR hx
  rw [mem_closedBall_zero_iff, norm_pow] at h
  rw [mem_closedBall_zero_iff]
  have h2 := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg x)] at h2

theorem val_mul_apply {R : Type*} [CommRing R] (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_scalar_mul_diagUnits2 {R : Type*} [CommRing R] (b a : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (b : R) ^ 2 * a := by
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (b : R) := rfl
  rw [Units.val_mul, Matrix.det_mul, h, Matrix.scalar_apply, Matrix.det_diagonal, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    Matrix.det_fin_two]
  simp [Fin.prod_univ_two]

theorem det_inv_scalar_mul_diagUnits2 {R : Type*} [CommRing R] (b a : Rˣ) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      ((b⁻¹ : Rˣ) : R) ^ 2 * ((a⁻¹ : Rˣ) : R) := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) R)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) b⁻¹ * diagUnits2 a⁻¹ 1 := by
    rw [mul_inv_rev, map_inv]
    have hd : (diagUnits2 a 1 : GL (Fin 2) R)⁻¹ = diagUnits2 a⁻¹ 1 := by
      rw [inv_eq_iff_mul_eq_one]
      apply Units.ext
      rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
        Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hd]

    apply Units.ext
    have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
        Matrix.scalar (Fin 2) ((b⁻¹ : Rˣ) : R) := rfl
    simp only [Units.val_mul, h]
    exact ((Matrix.scalar_commute ((b⁻¹ : Rˣ) : R) (fun r' => mul_comm _ _) _).eq).symm
  rw [hinv, det_scalar_mul_diagUnits2]

theorem det_toTensorGL (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((γ : Matrix (Fin 2) (Fin 2) A).det) := by
  rw [RingHom.map_det]
  rfl

theorem det_val_conj {R : Type*} [CommRing R] (x g : GL (Fin 2) R) :
    ((x⁻¹ * g * x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (g : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

end TwS6a

namespace TwWindowR2

open AutomorphicForm TwS6a

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
  (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

theorem norm_le_of_quadratic {F : Type*} [NormedField F] {r s d : F} (h : r * r = s * r - d) :
    ‖r‖ ≤ ‖s‖ + ‖d‖ + 1 := by
  by_contra H
  push_neg at H
  have h1 : 1 ≤ ‖r‖ := by linarith [norm_nonneg s, norm_nonneg d]
  have h2 : ‖r‖ * ‖r‖ ≤ ‖s‖ * ‖r‖ + ‖d‖ := by
    rw [← norm_mul, h]
    exact (norm_sub_le _ _).trans (by rw [norm_mul])
  nlinarith [norm_nonneg d, norm_nonneg s]

theorem real_bounds {na nb D' B : ℝ} (hna : 0 < na) (hnb : 0 < nb) (hD' : 1 ≤ D') (hB : 1 ≤ B)
    (hlow : D'⁻¹ ≤ na * nb) (ha : na ≤ B) (hb : nb ≤ B) :
    D'⁻¹ / B ≤ na ∧ D'⁻¹ / B ≤ nb ∧ (D'⁻¹ / B) / B ≤ nb / na ∧ nb / na ≤ B / (D'⁻¹ / B) := by
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D'⁻¹ := by positivity
  have hm0 : 0 < D'⁻¹ / B := by positivity
  have hla : D'⁻¹ / B ≤ na := by
    rw [div_le_iff₀ hB0]
    calc D'⁻¹ ≤ na * nb := hlow
      _ ≤ na * B := mul_le_mul_of_nonneg_left hb hna.le
  have hlb : D'⁻¹ / B ≤ nb := by
    rw [div_le_iff₀ hB0]
    calc D'⁻¹ ≤ na * nb := hlow
      _ ≤ B * nb := mul_le_mul_of_nonneg_right ha hnb.le
      _ = nb * B := mul_comm _ _
  refine ⟨hla, hlb, ?_, ?_⟩
  · rw [le_div_iff₀ hna]
    calc D'⁻¹ / B / B * na ≤ D'⁻¹ / B / B * B := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = D'⁻¹ / B := by field_simp
      _ ≤ nb := hlb
  · rw [div_le_iff₀ hna]
    calc nb ≤ B := hb
      _ = B / (D'⁻¹ / B) * (D'⁻¹ / B) := by field_simp
      _ ≤ B / (D'⁻¹ / B) * na := mul_le_mul_of_nonneg_left hla (by positivity)

omit σ φ in
theorem isCompact_annulus {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) :
    IsCompact {a : (v.adicCompletion K)ˣ | c₁ ≤ ‖(a : v.adicCompletion K)‖ ∧ ‖(a : v.adicCompletion K)‖ ≤ c₂} := by
  have hset : {a : (v.adicCompletion K)ˣ | c₁ ≤ ‖(a : v.adicCompletion K)‖ ∧ ‖(a : v.adicCompletion K)‖ ≤ c₂} =
      (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) ⁻¹' {x : v.adicCompletion K | c₁ ≤ ‖x‖ ∧ ‖x‖ ≤ c₂} := rfl
  rw [hset, Units.isEmbedding_val₀.isCompact_iff, Set.image_preimage_eq_inter_range]
  have hsub : {x : v.adicCompletion K | c₁ ≤ ‖x‖ ∧ ‖x‖ ≤ c₂} ⊆ Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
    intro x hx
    have hx1 : c₁ ≤ ‖x‖ := hx.1
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx1
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  rw [Set.inter_eq_left.2 hsub]
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : v.adicCompletion K) c₂)
  · exact isClosed_Icc.preimage continuous_norm
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx.2

theorem det_diagUnits2 {R : Type*} [CommRing R] (a b : Rˣ) :
    ((diagUnits2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (a : R) * (b : R) := by
  simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.det_fin_two]

theorem det_inv_diagUnits2 {R : Type*} [CommRing R] (a b : Rˣ) :
    (((diagUnits2 a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = ((a⁻¹ : Rˣ) : R) * ((b⁻¹ : Rˣ) : R) := by
  have h : (((diagUnits2 a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)] := rfl
  rw [h, Matrix.det_fin_two]
  simp

theorem trace_toTensorGL_diagUnits2 (a b : (v.adicCompletion K)ˣ) :
    Matrix.trace ((toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) ((a : v.adicCompletion K) + (b : v.adicCompletion K)) := by
  rw [Matrix.trace_fin_two, map_add]
  rfl

theorem trace_val_conj {R : Type*} [CommRing R] (x g : GL (Fin 2) R) :
    Matrix.trace ((x⁻¹ * g * x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) := by
  rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]

theorem invariants [FiniteDimensional K L] (a b : (v.adicCompletion K)ˣ) (x δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hN : normString K L (v.adicCompletion K) σ δ = toTensorGL K L (v.adicCompletion K) (diagUnits2 a b)) :
    Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        (((normString K L (v.adicCompletion K) σ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) =
      (Module.finrank K L : v.adicCompletion K) * ((a : v.adicCompletion K) * (b : v.adicCompletion K)) ∧
    Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        ((((normString K L (v.adicCompletion K) σ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x))⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) =
      (Module.finrank K L : v.adicCompletion K) * (((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * ((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∧
    Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        (Matrix.trace ((normString K L (v.adicCompletion K) σ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      (Module.finrank K L : v.adicCompletion K) * ((a : v.adicCompletion K) + (b : v.adicCompletion K)) := by
  have hNy : normString K L (v.adicCompletion K) σ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
      x⁻¹ * toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) * x := by
    rw [normString_conj, hN]
  have hfr : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = Module.finrank K L := TensorProduct.finrank_rightAlgebra L
  refine ⟨?_, ?_, ?_⟩
  · rw [hNy, det_val_conj, det_toTensorGL, det_diagUnits2]
    show Algebra.trace _ _ (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _) = _
    rw [Algebra.trace_algebraMap, hfr, nsmul_eq_mul]
  · have hinv : (normString K L (v.adicCompletion K) σ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x))⁻¹ =
        x⁻¹ * (toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))⁻¹ * x := by
      rw [hNy]; group
    rw [hinv, det_val_conj, ← map_inv, det_toTensorGL, det_inv_diagUnits2]
    show Algebra.trace _ _ (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _) = _
    rw [Algebra.trace_algebraMap, hfr, nsmul_eq_mul]
  · rw [hNy, trace_val_conj, trace_toTensorGL_diagUnits2, Algebra.trace_algebraMap, hfr, nsmul_eq_mul]

theorem exists_conj_mem_tsupport {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    {τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)}
    {J : ℂ} (hJ : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φ J) (hJ0 : J ≠ 0) :
    ∃ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x ∈ tsupport φ := by
  obtain ⟨s, hs, hJeq⟩ := hJ
  have hexx : ∃ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hJ0
    rw [hJeq]
    simp only [hall, zero_mul, integral_zero]
  obtain ⟨x, hx⟩ := hexx
  exact ⟨x, subset_tsupport _ hx⟩

theorem norm_le_of_norm_mul_le {F : Type*} [NormedField F] {c z : F} {R : ℝ} (hc : 0 < ‖c‖) (h : ‖c * z‖ ≤ R) :
    ‖z‖ ≤ max R 0 / ‖c‖ := by
  rw [le_div_iff₀ hc, norm_mul] at *
  calc ‖z‖ * ‖c‖ = ‖c‖ * ‖z‖ := mul_comm _ _
    _ ≤ R := h
    _ ≤ max R 0 := le_max_left _ _

theorem Φ_support [FiniteDimensional K L] [IsGalois K L]
    (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ S : Set ((v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ), IsCompact S ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → Φ K L σ v φ (a, t) ≠ 0 → (a, t) ∈ S := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hℓn : 0 < ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.mpr (Module.finrank_pos).ne')
  have htrc : Continuous (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) := IsModuleTopology.continuous_of_linearMap _
  have hNc : Continuous (normString K L (v.adicCompletion K) σ) := by
    have := continuous_P K L (v.adicCompletion K) σ (Module.finrank K L)
    exact this

  let h₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → v.adicCompletion K := fun y => Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
    (((normString K L (v.adicCompletion K) σ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det)
  let h₂ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → v.adicCompletion K := fun y => Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
    ((((normString K L (v.adicCompletion K) σ y)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det)
  let h₃ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → v.adicCompletion K := fun y => Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
    (Matrix.trace ((normString K L (v.adicCompletion K) σ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
  have hh₁c : Continuous h₁ := htrc.comp ((Units.continuous_val.comp hNc).matrix_det)
  have hh₂c : Continuous h₂ := htrc.comp ((Units.continuous_coe_inv.comp hNc).matrix_det)
  have hh₃c : Continuous h₃ := htrc.comp ((Units.continuous_val.comp hNc).matrix_trace)
  have hS : IsCompact (tsupport φ) := hφ.2
  obtain ⟨R₁, hR₁⟩ := hS.exists_bound_of_continuousOn hh₁c.continuousOn
  obtain ⟨R₂, hR₂⟩ := hS.exists_bound_of_continuousOn hh₂c.continuousOn
  obtain ⟨R₃, hR₃⟩ := hS.exists_bound_of_continuousOn hh₃c.continuousOn

  set ℓn : ℝ := ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ with hℓn'
  set D : ℝ := max R₁ 0 / ℓn with hD
  set D' : ℝ := max (max R₂ 0 / ℓn) 1 with hD'
  set Sb : ℝ := max R₃ 0 / ℓn with hSb
  set B : ℝ := Sb + D + 1 with hB
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hSb0 : 0 ≤ Sb := by rw [hSb]; positivity
  have hD'1 : 1 ≤ D' := le_max_right _ _
  have hD'0 : 0 < D' := by linarith
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hB0 : 0 < B := by linarith
  have hm0 : 0 < D'⁻¹ / B := by positivity
  refine ⟨{a : (v.adicCompletion K)ˣ | D'⁻¹ / B ≤ ‖(a : v.adicCompletion K)‖ ∧ ‖(a : v.adicCompletion K)‖ ≤ B} ×ˢ
      {t : (v.adicCompletion K)ˣ | D'⁻¹ / B / B ≤ ‖(t : v.adicCompletion K)‖ ∧ ‖(t : v.adicCompletion K)‖ ≤ B / (D'⁻¹ / B)},
    (isCompact_annulus K v hm0).prod (isCompact_annulus K v (by positivity)), ?_⟩
  intro a t ht hΦ

  have hex : ∃ J : ℂ, TwWindow.P K L σ v φ a t J := by
    by_contra h; exact hΦ (Φ_eq_zero_of_not K L σ v φ h)
  obtain ⟨J₀, hJ₀⟩ := hex
  obtain ⟨α, β, hN, τ', hτ', hτ'1, hJ⟩ := Φ_spec_of_P K L σ v φ hJ₀
  obtain ⟨x, hyS⟩ := exists_conj_mem_tsupport K L σ v φ hJ hΦ
  obtain ⟨e₁, e₂, e₃⟩ := invariants K L σ v a (a * t) x (diagUnits2 α β) hN

  have hb₁ : ‖(a : v.adicCompletion K) * ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ D :=
    norm_le_of_norm_mul_le hℓn (by rw [← e₁]; exact hR₁ _ hyS)
  have hb₂ : ‖((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * (((a * t)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ max R₂ 0 / ℓn :=
    norm_le_of_norm_mul_le hℓn (by rw [← e₂]; exact hR₂ _ hyS)
  have hb₃ : ‖(a : v.adicCompletion K) + ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ Sb :=
    norm_le_of_norm_mul_le hℓn (by rw [← e₃]; exact hR₃ _ hyS)
  have hapos : 0 < ‖(a : v.adicCompletion K)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hatpos : 0 < ‖((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hlow : D'⁻¹ ≤ ‖(a : v.adicCompletion K)‖ * ‖((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ := by
    have h : (‖(a : v.adicCompletion K)‖ * ‖((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖)⁻¹ ≤ D' := by
      rw [← norm_mul, ← norm_inv, mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_inv_eq_inv_val]
      exact hb₂.trans (le_max_left _ _)
    exact (inv_le_comm₀ (mul_pos hapos hatpos) hD'0).1 h
  have hra : ‖(a : v.adicCompletion K)‖ ≤ B := by
    have hq : (a : v.adicCompletion K) * (a : v.adicCompletion K) =
        ((a : v.adicCompletion K) + ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)) * (a : v.adicCompletion K) - (a : v.adicCompletion K) * ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
      ring
    have := norm_le_of_quadratic hq
    rw [hB]; linarith
  have hrat : ‖((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ B := by
    have hq : ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) * ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        ((a : v.adicCompletion K) + ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)) * ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) -
          (a : v.adicCompletion K) * ((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
      ring
    have := norm_le_of_quadratic hq
    rw [hB]; linarith
  obtain ⟨hla, -, ht1, ht2⟩ := real_bounds hapos hatpos hD'1 hB1 hlow hra hrat
  have hnt : ‖(t : v.adicCompletion K)‖ = ‖((a * t : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ / ‖(a : v.adicCompletion K)‖ := by
    rw [Units.val_mul, norm_mul, mul_comm, mul_div_cancel_right₀ _ hapos.ne']
  refine Set.mk_mem_prod ⟨hla, hra⟩ ⟨?_, ?_⟩
  · show D'⁻¹ / B / B ≤ ‖(t : v.adicCompletion K)‖
    rw [hnt]; exact ht1
  · show ‖(t : v.adicCompletion K)‖ ≤ B / (D'⁻¹ / B)
    rw [hnt]; exact ht2

end TwWindowR2

open TwWindowR2 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      (∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Φ q = Φ p) ∧
      (∃ S : Set ((v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ), IsCompact S ∧
        ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → Φ (a, t) ≠ 0 → (a, t) ∈ S) ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
        (∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
            AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
          ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
            τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
          ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
            J' = Φ (a, t)) ∧
        ((¬ ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
            AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) →
          Φ (a, t) = 0) := by
  refine ⟨TwWindowR2.Φ K L σ v φ, ?_, ?_, ?_⟩
  · exact fun p hp => TwWindowR2.Φ_locallyConstant K L σ v φ hgen hφ p hp
  · exact TwWindowR2.Φ_support K L σ v φ hφ
  · intro a t ht
    refine ⟨fun α β hN τ' hτ' hτ'1 J' hJ' => ?_, fun hno => ?_⟩
    · have hP : TwWindow.P K L σ v φ a t J' := ⟨α, β, hN, τ', hτ', hτ'1, hJ'⟩
      exact TwWindowR2.P_unique K L σ v φ hgen hφ ht hP (TwWindowR2.Φ_spec_of_P K L σ v φ hP)
    · apply TwWindowR2.Φ_eq_zero_of_not
      rintro ⟨J, α, β, hN, -⟩
      exact hno ⟨α, β, hN⟩

end S_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn (solution)
