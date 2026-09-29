-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b880a4b4-651b-5627-a6f5-28a7e88eb23e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
import Theorems.Thm_AutomorphicForm_exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem
import Theorems.Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
import Theorems.Thm_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AVKProof

variable (K : Type) [Field K] [NumberField K]

local notation "G" => AdelicGL2 (𝓞 K) K
local notation "𝐊" => adelicMaximalCompact K

def detAt (w : InfinitePlace K) : G →* (w.Completion)ˣ :=
  Matrix.GeneralLinearGroup.det.comp ((archComponent K w).comp (NumberField.AdelicLevel.glArch (𝓞 K) K))

theorem detAt_eq_one_iff (w : InfinitePlace K) (k : G) :
    detAt K w k = 1 ↔
      ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
  rw [detAt, MonoidHom.comp_apply, MonoidHom.comp_apply, ← Units.val_eq_one,
    Matrix.GeneralLinearGroup.val_det_apply]

theorem continuous_detAt (w : InfinitePlace K) : Continuous (detAt K w) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h1 : Continuous fun g : G =>
        ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) :=
      Units.continuous_val.comp ((continuous_archComponent K w).comp (NumberField.AdelicLevel.continuous_glArch (𝓞 K) K))
    simpa [detAt, Function.comp_def, Matrix.GeneralLinearGroup.val_det_apply] using h1.matrix_det
  · have h1 : Continuous fun g : G =>
        ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K g⁻¹) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) :=
      Units.continuous_val.comp ((continuous_archComponent K w).comp
        ((NumberField.AdelicLevel.continuous_glArch (𝓞 K) K).comp continuous_inv))
    have : (fun g : G => ((detAt K w g)⁻¹ : (w.Completion)ˣ).val) =
        fun g => ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K g⁻¹) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
      funext g; rw [← map_inv]; simp [detAt]
    rw [this]; exact h1.matrix_det

def Kp : Subgroup 𝐊 :=
  ⨅ w : {w : InfinitePlace K // w.IsReal}, ((detAt K w.1).comp (adelicMaximalCompact K).subtype).ker

theorem mem_Kp_iff (k : 𝐊) :
    k ∈ Kp K ↔ ∀ w : InfinitePlace K, w.IsReal →
      ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K (k : G)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
  simp only [Kp, Subgroup.mem_iInf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply,
    detAt_eq_one_iff, Subtype.forall]

theorem isClosed_Kp : IsClosed (Kp K : Set 𝐊) := by
  have h : (Kp K : Set 𝐊) = ⋂ w : {w : InfinitePlace K // w.IsReal},
      ((detAt K w.1).comp (adelicMaximalCompact K).subtype) ⁻¹' {1} := by
    ext k
    simp only [Kp, SetLike.mem_coe, Subgroup.mem_iInf, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [h]
  exact isClosed_iInter fun w => isClosed_singleton.preimage
    ((continuous_detAt K w.1).comp continuous_subtype_val)

scoped instance secondCountable_K : SecondCountableTopology 𝐊 := by
  haveI : SecondCountableTopology G := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  exact TopologicalSpace.Subtype.secondCountableTopology _

scoped instance secondCountable_Kp : SecondCountableTopology (Kp K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance compactSpace_Kp : CompactSpace (Kp K) :=
  isCompact_iff_compactSpace.mp (isClosed_Kp K).isCompact

def μp : Measure (Kp K) := Measure.haarMeasure ⊤

scoped instance isHaar_μp : (μp K).IsHaarMeasure := by rw [μp]; infer_instance
scoped instance isProb_μp : IsProbabilityMeasure (μp K) :=
  ⟨by rw [μp, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
scoped instance isRight_μp : (μp K).IsMulRightInvariant :=
  MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact {1} Set.univ
    (fun z hz g => by rw [Set.mem_singleton_iff.mp hz, mul_one, one_mul]) isCompact_univ
    (fun g => ⟨1, Set.mem_singleton _, g, Set.mem_univ _, (one_mul g).symm⟩) (μp K)
scoped instance isInv_μp : (μp K).IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (μp K)

scoped instance isRight_μK : (maximalCompactHaar K).IsMulRightInvariant :=
  MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact {1} Set.univ
    (fun z hz g => by rw [Set.mem_singleton_iff.mp hz, mul_one, one_mul]) isCompact_univ
    (fun g => ⟨1, Set.mem_singleton _, g, Set.mem_univ _, (one_mul g).symm⟩) (maximalCompactHaar K)
scoped instance isInv_μK : (maximalCompactHaar K).IsInvInvariant :=
  MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (maximalCompactHaar K)

def νp : Measure (Kp K) := Measure.comap ((↑) : Kp K → 𝐊) (maximalCompactHaar K)

theorem measurableEmbedding_val : MeasurableEmbedding ((↑) : Kp K → 𝐊) :=
  MeasurableEmbedding.subtype_coe (isClosed_Kp K).measurableSet

scoped instance isLeft_νp : (νp K).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  apply Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul g) hs, νp,
    (measurableEmbedding_val K).comap_apply, (measurableEmbedding_val K).comap_apply]
  have : ((↑) : Kp K → 𝐊) '' ((fun x => g * x) ⁻¹' s) = (fun x => (g : 𝐊) * x) ⁻¹' (((↑) : Kp K → 𝐊) '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x, hx, by simp⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨g⁻¹ * x, ?_, ?_⟩
      · show g * (g⁻¹ * x) ∈ s
        rwa [mul_inv_cancel_left]
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hxy, inv_mul_cancel_left]
  rw [this, ← Measure.map_apply (measurable_const_mul (g : 𝐊))
    ((measurableEmbedding_val K).measurableSet_image.mpr hs), MeasureTheory.map_mul_left_eq_self]

scoped instance isFinite_νp : IsFiniteMeasure (νp K) := by
  refine ⟨?_⟩
  rw [νp, (measurableEmbedding_val K).comap_apply]
  exact measure_lt_top _ _

theorem νp_eq_smul : νp K = (maximalCompactHaar K) (Kp K : Set 𝐊) • μp K := by
  have h := MeasureTheory.Measure.haarMeasure_unique (νp K) (⊤ : TopologicalSpace.PositiveCompacts (Kp K))
  rw [μp]
  convert h using 2
  rw [TopologicalSpace.PositiveCompacts.coe_top, νp, (measurableEmbedding_val K).comap_apply, Set.image_univ,
    Subtype.range_coe_subtype]
  rfl

theorem integral_eq_of_support (F : 𝐊 → ℂ) (hF : ∀ k : 𝐊, k ∉ Kp K → F k = 0) :
    ∫ k, F k ∂(maximalCompactHaar K) =
      ((maximalCompactHaar K) (Kp K : Set 𝐊)).toReal * ∫ k, F (k : 𝐊) ∂(μp K) := by
  have hind : (Kp K : Set 𝐊).indicator F = F := by
    funext k
    by_cases hk : k ∈ (Kp K : Set 𝐊)
    · rw [Set.indicator_of_mem hk]
    · rw [Set.indicator_of_notMem hk, hF k hk]
  have hs := (isClosed_Kp K).measurableSet
  calc ∫ k, F k ∂(maximalCompactHaar K)
      = ∫ k in (Kp K : Set 𝐊), F k ∂(maximalCompactHaar K) := by rw [← integral_indicator hs, hind]
    _ = ∫ k : Kp K, F (k : 𝐊) ∂(νp K) := (integral_subtype_comap hs F).symm
    _ = ((maximalCompactHaar K) (Kp K : Set 𝐊)).toReal * ∫ k, F (k : 𝐊) ∂(μp K) := by
        rw [νp_eq_smul, integral_smul_measure, Complex.real_smul]

theorem det_eq_one_or (k : 𝐊) (w : InfinitePlace K) (hw : w.IsReal) :
    ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K (k : G)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 ∨
    ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K (k : G)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = -1 := by
  have hn := ((mem_adelicMaximalCompact_iff.mp k.2).2 w).1
  set d := ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K (k : G)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det with hd
  let eR := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  have h1 : |eR d| = 1 := by
    have : dist (eR d) (eR 0) = dist d 0 := eR.dist_eq d 0
    rw [dist_zero_right, hn, Real.dist_eq] at this
    have h0 : eR 0 = 0 := map_zero (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
    rwa [h0, sub_zero] at this
  have hinj : Function.Injective eR := eR.injective
  rcases abs_eq (zero_le_one) |>.mp h1 with h | h
  · left
    apply hinj
    rw [h]; exact (map_one (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)).symm
  · right
    apply hinj
    rw [h, show eR (-1) = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw (-1) from rfl, map_neg, map_one]

theorem isOpen_Kp : IsOpen (Kp K : Set 𝐊) := by
  have hne : (1 : ℂ) ≠ -1 := by norm_num
  have h : (Kp K : Set 𝐊) = ⋂ w : {w : InfinitePlace K // w.IsReal},
      (fun k : 𝐊 => (((detAt K w.1 (k : G)) : (w.1.Completion)ˣ) : w.1.Completion)) ⁻¹' {-1}ᶜ := by
    ext k
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      Subtype.forall]
    rw [mem_Kp_iff]
    refine forall_congr' fun w => forall_congr' fun hw => ?_
    have hval : (((detAt K w (k : G)) : (w.Completion)ˣ) : w.Completion) =
        ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K (k : G)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
      simp [detAt]
    rw [hval]
    have h12 : (1 : w.Completion) ≠ -1 := by
      intro h
      have : (2 : w.Completion) = 0 := by
        calc (2 : w.Completion) = 1 + 1 := by norm_num
          _ = 1 + -1 := by rw [← h]
          _ = 0 := by ring
      have h2 := congrArg (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) this
      rw [map_ofNat, map_zero] at h2
      norm_num at h2
    constructor
    · intro h1; rw [h1]; exact h12
    · intro hne1
      rcases det_eq_one_or K k w hw with h | h
      · exact h
      · exact absurd h hne1
  rw [h]
  refine isOpen_iInter_of_finite fun w => ?_
  exact (isOpen_compl_singleton).preimage
    (Units.continuous_val.comp ((continuous_detAt K w.1).comp continuous_subtype_val))

theorem archRowIsometrySubgroup_le (w : InfinitePlace K) :
    archRowIsometrySubgroup K w ≤ adelicMaximalCompact K := by
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_adelicMaximalCompact_iff']
  refine ⟨?_, fun v => ?_⟩
  · show NumberField.AdelicLevel.glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w k)) ∈ _
    rw [glFin_adelicArchGLIncl]
    exact Subgroup.one_mem _
  · show archComponent K v (NumberField.AdelicLevel.glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w k))) ∈ _
    rw [glArch_adelicArchGLIncl]
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_archGLIncl_self]
      exact hk
    · rw [archComponent_archGLIncl_of_ne K hvw]
      exact Subgroup.one_mem _

theorem level_le (N : Ideal (𝓞 K)) :
    principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ≤ adelicMaximalCompact K := by
  intro u hu
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  have hl : NumberField.AdelicLevel.glFin (𝓞 K) K u ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 K) K N :=
    NumberField.AdelicLevel.mem_levelOne_iff.mp (principalLevel_le_levelOne (𝓞 K) K N hu1)
  rw [mem_adelicMaximalCompact_iff']
  refine ⟨NumberField.AdelicLevel.mem_finiteIntegralGL2_iff.mpr ⟨hl.1.integral, hl.2.integral⟩, fun w => ?_⟩
  rw [(mem_finiteAdelicGL2Subgroup_iff K u).mp hu2, map_one]
  exact Subgroup.one_mem _

theorem integrable_of_continuous {f : 𝐊 → ℂ} (hf : Continuous f) : Integrable f (maximalCompactHaar K) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

section UnitLemmas
variable {K}

theorem unit_conj_eq (E' : Submodule ℂ (Kp K → ℂ)) (e : Kp K → ℂ)
    (hE'r : ∀ k : Kp K, ∀ v ∈ E', (fun x => v (x * k)) ∈ E')
    (hE'l : ∀ k : Kp K, ∀ v ∈ E', (fun x => v (k * x)) ∈ E')
    (hE's : ∀ v ∈ E', (fun x => conj (v x⁻¹)) ∈ E')
    (heinv : (fun k => e k⁻¹) ∈ E')
    (hesymm : ∀ k : Kp K, e k⁻¹ = conj (e k))
    (hefix : ∀ v ∈ E', ∀ x : Kp K, ∫ k, e k * v (x * k) ∂(μp K) = v x)
    (k₀ x : Kp K) : e (k₀ * x * k₀⁻¹) = e x := by

  have heleft : ∀ v ∈ E', ∀ x : Kp K, ∫ k, e k * v (k * x) ∂(μp K) = v x := by
    intro v hv x
    have h := hefix _ (hE's v hv) x⁻¹
    simp only [mul_inv_rev, inv_inv] at h
    have h2 := congrArg conj h
    rw [← integral_conj] at h2
    simp only [map_mul, Complex.conj_conj] at h2
    have h3 : ∫ k, e k⁻¹ * v (k⁻¹ * x) ∂(μp K) = v x := by
      rw [← h2]; congr 1; funext k; rw [hesymm]
    rwa [MeasureTheory.integral_inv_eq_self (fun k => e k * v (k * x))] at h3

  have hunit : ∀ v ∈ E', ∀ z : Kp K, ∫ y, e (k₀ * y * k₀⁻¹) * v (z * y) ∂(μp K) = v z := by
    intro v hv z
    have hvt : (fun t => v (t * k₀)) ∈ E' := hE'r k₀ v hv
    have h := hefix _ hvt (z * k₀⁻¹)
    simp only [inv_mul_cancel_right] at h

    set F : Kp K → ℂ := fun u => e u * v (z * k₀⁻¹ * u * k₀) with hF
    have h1 := MeasureTheory.integral_mul_left_eq_self (μ := μp K) (fun t => F (t * k₀⁻¹)) k₀
    have h2 := MeasureTheory.integral_mul_right_eq_self (μ := μp K) F k₀⁻¹
    beta_reduce at h1
    calc ∫ y, e (k₀ * y * k₀⁻¹) * v (z * y) ∂(μp K) = ∫ y, F (k₀ * y * k₀⁻¹) ∂(μp K) := by
          congr 1; funext y; simp only [hF, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
      _ = ∫ y, F y ∂(μp K) := by rw [h1, h2]
      _ = v z := h
  have hw' : (fun k => e k⁻¹) ∈ E' := heinv
  have hu : (fun y => e (k₀ * y⁻¹ * k₀⁻¹)) ∈ E' := by
    have h := hE'r k₀⁻¹ _ (hE'l k₀ _ hw')
    have heq : (fun y => e (k₀ * y⁻¹ * k₀⁻¹)) =
        (fun x => (fun x' => (fun k => e k⁻¹) (k₀ * x')) (x * k₀⁻¹)) := by
      funext y; simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [heq]; exact h

  have I1 := heleft _ hu x⁻¹

  have I2 := hunit _ hw' x⁻¹
  simp only [mul_inv_rev, inv_inv] at I1 I2
  have I2' : ∫ y, e y * e (k₀ * (x * y⁻¹) * k₀⁻¹) ∂(μp K) = e x := by
    rw [← I2]
    set F : Kp K → ℂ := fun y => e (k₀ * y * k₀⁻¹) * e (y⁻¹ * x) with hF
    have h1 := MeasureTheory.integral_inv_eq_self (μ := μp K) F
    have h2 := MeasureTheory.integral_mul_right_eq_self (μ := μp K) (fun y => F y⁻¹) x⁻¹
    beta_reduce at h2
    rw [show (∫ y, e (k₀ * y * k₀⁻¹) * e (y⁻¹ * x) ∂(μp K)) = ∫ y, F y ∂(μp K) from rfl, ← h1, ← h2]
    congr 1
    funext y
    simp only [hF, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one, mul_comm (e y)]
  calc e (k₀ * x * k₀⁻¹) = ∫ y, e y * e (k₀ * (x * y⁻¹) * k₀⁻¹) ∂(μp K) := by
        rw [← I1]
        try (congr 1; funext y; simp only [mul_assoc])
    _ = e x := I2'

theorem integral_comm_of_conj {κ : 𝐊 → ℂ}
    (hκconj : ∀ (k₀ : Kp K) (k : 𝐊), κ ((k₀ : 𝐊) * k * (k₀ : 𝐊)⁻¹) = κ k)
    (φ : G → ℂ) (k : 𝐊) (hk : k ∈ Kp K) (g : G) :
    (∫ k', κ k' * φ (g * (k' : G) * (k : G)) ∂(maximalCompactHaar K)) =
      ∫ k', κ k' * φ (g * (k : G) * (k' : G)) ∂(maximalCompactHaar K) := by
  set Gf : 𝐊 → ℂ := fun k' => κ k' * φ (g * (k' : G) * (k : G)) with hGf
  have h1 := MeasureTheory.integral_mul_left_eq_self (μ := maximalCompactHaar K) (fun t => Gf (t * k⁻¹)) k
  have h2 := MeasureTheory.integral_mul_right_eq_self (μ := maximalCompactHaar K) Gf k⁻¹
  beta_reduce at h1
  symm
  calc ∫ k', κ k' * φ (g * (k : G) * (k' : G)) ∂(maximalCompactHaar K) = ∫ u, Gf (k * u * k⁻¹) ∂(maximalCompactHaar K) := by
        congr 1; funext u
        have hk' : κ (k * u * k⁻¹) = κ u := hκconj ⟨k, hk⟩ u
        simp only [hGf]
        rw [hk']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]
    _ = ∫ u, Gf u ∂(maximalCompactHaar K) := by rw [h1, h2]

theorem average_average_eq {κ : 𝐊 → ℂ} (hκc : Continuous κ)
    (hconv : ∀ k, ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k)
    {φ : G → ℂ} (hφc : Continuous φ) (g : G) :
    (∫ k, κ k * (∫ k', κ k' * φ (g * (k : G) * (k' : G)) ∂(maximalCompactHaar K)) ∂(maximalCompactHaar K)) =
      ∫ k, κ k * φ (g * (k : G)) ∂(maximalCompactHaar K) := by
  have hφk : ∀ x : G, Continuous fun k : 𝐊 => φ (x * (k : G)) :=
    fun x => hφc.comp (continuous_const.mul continuous_subtype_val)
  have hinner : ∀ k : 𝐊,
      ∫ k', κ k' * φ (g * (k : G) * (k' : G)) ∂(maximalCompactHaar K) =
        ∫ k'', κ (k⁻¹ * k'') * φ (g * (k'' : G)) ∂(maximalCompactHaar K) := by
    intro k
    rw [← MeasureTheory.integral_mul_left_eq_self
      (fun k'' : 𝐊 => κ (k⁻¹ * k'') * φ (g * (k'' : G))) k]
    congr 1
    funext k'
    simp only [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]
  simp_rw [hinner, ← integral_const_mul, ← mul_assoc]
  have hF : Continuous fun p : 𝐊 × 𝐊 => κ p.1 * κ (p.1⁻¹ * p.2) * φ (g * (p.2 : G)) :=
    ((hκc.comp continuous_fst).mul (hκc.comp ((continuous_fst.inv).mul continuous_snd))).mul
      ((hφk g).comp continuous_snd)
  have hI : Integrable (fun p : 𝐊 × 𝐊 => κ p.1 * κ (p.1⁻¹ * p.2) * φ (g * (p.2 : G)))
      ((maximalCompactHaar K).prod (maximalCompactHaar K)) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_integral_swap hI]
  refine integral_congr_ae (ae_of_all _ fun k'' => ?_)
  simp only
  rw [integral_mul_const, hconv]

theorem average_translate {κ : 𝐊 → ℂ} (φ : G → ℂ) (x : G) (k₀ : 𝐊) :
    (∫ k, κ k * φ (x * (k₀ : G) * (k : G)) ∂(maximalCompactHaar K)) =
      ∫ k, κ (k₀⁻¹ * k) * φ (x * (k : G)) ∂(maximalCompactHaar K) := by
  rw [← MeasureTheory.integral_mul_left_eq_self
    (fun k : 𝐊 => κ (k₀⁻¹ * k) * φ (x * (k : G))) k₀]
  congr 1
  funext k
  simp only [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]

theorem continuous_average {κ : 𝐊 → ℂ} (hκc : Continuous κ) {φ : G → ℂ} (hφc : Continuous φ) :
    Continuous fun g : G => ∫ k, κ k * φ (g * (k : G)) ∂(maximalCompactHaar K) := by
  haveI : SecondCountableTopology G := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hj : Continuous (Function.uncurry fun (x : G) (k : 𝐊) => κ k * φ (x * (k : G))) :=
    (hκc.comp continuous_snd).mul (hφc.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have h := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hj isCompact_univ
  simpa only [Measure.restrict_univ] using h

open scoped Classical in

theorem average_mem_span {φ : G → ℂ} (hφc : Continuous φ) (c : ℂ) (S : Finset (G → ℂ))
    (hSc : ∀ s ∈ S, Continuous fun k : 𝐊 => s (k : G)) (u : G → ℂ)
    (hu : u ∈ Submodule.span ℂ (S : Set (G → ℂ))) :
    (fun x => ∫ k, c * conj (u (k : G)) * φ (x * (k : G)) ∂(maximalCompactHaar K)) ∈
      Submodule.span ℂ ((S.image fun s x => ∫ k, c * conj (s (k : G)) * φ (x * (k : G)) ∂(maximalCompactHaar K) :
        Finset (G → ℂ)) : Set (G → ℂ)) := by
  classical
  have hφk : ∀ x : G, Continuous fun k : 𝐊 => φ (x * (k : G)) :=
    fun x => hφc.comp (continuous_const.mul continuous_subtype_val)
  set Ψ : (G → ℂ) → (G → ℂ) := fun u x => ∫ k, c * conj (u (k : G)) * φ (x * (k : G)) ∂(maximalCompactHaar K)
    with hΨ
  suffices h : (Continuous fun k : 𝐊 => u (k : G)) ∧ Ψ u ∈ Submodule.span ℂ ((S.image Ψ : Finset _) : Set (G → ℂ)) by
    exact h.2
  induction hu using Submodule.span_induction with
  | mem s hs =>
    exact ⟨hSc s hs, Submodule.subset_span (by simpa using Finset.mem_image_of_mem Ψ hs)⟩
  | zero =>
    refine ⟨continuous_const, ?_⟩
    have : Ψ 0 = 0 := by funext x; simp [hΨ]
    rw [this]; exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
    refine ⟨hu.1.add hv.1, ?_⟩
    have : Ψ (u + v) = Ψ u + Ψ v := by
      funext x
      simp only [hΨ, Pi.add_apply, map_add, mul_add, add_mul]
      exact integral_add
        (integrable_of_continuous K ((continuous_const.mul (Complex.continuous_conj.comp hu.1)).mul (hφk x)))
        (integrable_of_continuous K ((continuous_const.mul (Complex.continuous_conj.comp hv.1)).mul (hφk x)))
    rw [this]; exact Submodule.add_mem _ hu.2 hv.2
  | smul a u _ hu =>
    refine ⟨continuous_const.mul hu.1, ?_⟩
    have : Ψ (a • u) = conj a • Ψ u := by
      funext x
      simp only [hΨ, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← integral_const_mul]
      congr 1; funext k; ring
    rw [this]; exact Submodule.smul_mem _ _ hu.2

end UnitLemmas

section CutTransport
variable {K}

theorem continuous_archGLIncl (w : InfinitePlace K) : Continuous (archGLIncl K w) := by
  have hval : ∀ {f : GL (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) w.Completion}, Continuous f →
      Continuous fun k => archMatrixUpdate K w (f k) := by
    intro f hf
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    by_cases hv : v = w
    · subst hv
      simp only [archMatrixUpdate_apply_self]
      exact hf.matrix_elem i j
    · simp only [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      exact continuous_const
  rw [Units.continuous_iff]
  exact ⟨hval Units.continuous_val, hval Units.continuous_coe_inv⟩

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl K) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((adelicArchGLIncl K g : G) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :
          InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_inclAt (w : InfinitePlace K) : Continuous (adelicArchGLInclAt K w) := by
  show Continuous fun k => adelicArchGLIncl K (archGLIncl K w k)
  exact (continuous_adelicArchGLIncl (K := K)).comp (continuous_archGLIncl w)

theorem average_mem_archCutSubmodule (tys : ArchTypeFamily K) {wf : G → ℂ}
    (hwc : Continuous fun k : 𝐊 => wf (k : G))
    (hw0 : ∀ y : G, y ∉ adelicMaximalCompact K → wf y = 0)
    (hcut : (fun y => conj (wf y⁻¹)) ∈ archCutSubmodule K tys)
    (c : ℂ) {φ : G → ℂ} (hφc : Continuous φ) :
    (fun x => ∫ k, c * conj (wf (k : G)) * φ (x * (k : G)) ∂(maximalCompactHaar K)) ∈ archCutSubmodule K tys := by
  have hφk : ∀ x : G, Continuous fun k : 𝐊 => φ (x * (k : G)) :=
    fun x => hφc.comp (continuous_const.mul continuous_subtype_val)
  rw [mem_archCutSubmodule_iff]
  intro w₁
  change _ ∈ ⨆ i : Fin (tys.card w₁), typeSubmodule (rowIsometryInclAt₀ K w₁) (tys.rep w₁ i).ρ
  set ι := rowIsometryInclAt₀ K w₁ with hιdef
  set f : G → ℂ := fun y => conj (wf y⁻¹) with hf
  have hfmem : f ∈ ⨆ i : Fin (tys.card w₁), typeSubmodule ι (tys.rep w₁ i).ρ :=
    (mem_archCutSubmodule_iff K tys f).mp hcut w₁
  haveI : CompactSpace (rowIsometrySubgroup₀ w₁.Completion) :=
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne K w₁)
  obtain ⟨n, ρc, hρc, H⟩ :=
    AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
      (fun i : Fin (tys.card w₁) => (tys.rep w₁ i).ρ)
  have hιK : ∀ h : rowIsometrySubgroup₀ w₁.Completion, ι h ∈ adelicMaximalCompact K :=
    fun h => archRowIsometrySubgroup_le K w₁ ⟨(h : GL (Fin 2) w₁.Completion), rowIsometrySubgroup₀_le _ h.2, rfl⟩
  have hιc : Continuous ι := (continuous_inclAt w₁).comp continuous_subtype_val
  have hinj : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun g => archComponent K w₁ (NumberField.AdelicLevel.glArch (𝓞 K) K g)) hab
    simpa only [hιdef, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
      archComponent_archGLIncl_self] using this
  obtain ⟨H1, H2⟩ := H G ι hinj

  have hKiff : ∀ (y : G) (h : rowIsometrySubgroup₀ w₁.Completion), (y * ι h)⁻¹ ∈ adelicMaximalCompact K →
      y ∈ adelicMaximalCompact K := by
    intro y h hmem
    have h1 : y⁻¹ = ι h * (y * ι h)⁻¹ := by rw [mul_inv_rev, mul_inv_cancel_left]
    have : y⁻¹ ∈ adelicMaximalCompact K := by rw [h1]; exact (adelicMaximalCompact K).mul_mem (hιK h) hmem
    simpa using (adelicMaximalCompact K).inv_mem this

  have horb : ∀ y : G, Continuous fun h : rowIsometrySubgroup₀ w₁.Completion => f (y * ι h) := by
    intro y
    by_cases hy : y ∈ adelicMaximalCompact K
    · have : (fun h : rowIsometrySubgroup₀ w₁.Completion => f (y * ι h)) =
          (fun k : 𝐊 => conj (wf (k : G))) ∘ fun h =>
            ((⟨ι h, hιK h⟩ : 𝐊)⁻¹ * (⟨y, hy⟩ : 𝐊)⁻¹) := by
        funext h; simp only [hf, Function.comp_apply, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [this]
      have hiKc : Continuous fun h : rowIsometrySubgroup₀ w₁.Completion => (⟨ι h, hιK h⟩ : 𝐊) :=
        Continuous.subtype_mk hιc _
      exact (Complex.continuous_conj.comp hwc).comp (hiKc.inv.mul continuous_const)
    · have : (fun h : rowIsometrySubgroup₀ w₁.Completion => f (y * ι h)) = fun _ => 0 := by
        funext h
        simp only [hf]
        rw [hw0 _ (fun hmem => hy (hKiff y h hmem)), map_zero]
      rw [this]
      exact continuous_const
  obtain ⟨m, T, hT, hrange⟩ := H2 f hfmem horb
  have hf_range : f ∈ LinearMap.range T := by
    rw [hrange]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y; simp
  obtain ⟨x₀, hx₀⟩ := hf_range

  have hTcont : ∀ u, Continuous fun k : 𝐊 => (T u) ((k : G)⁻¹) := by
    intro u
    have hmem : T u ∈ Submodule.span ℂ (Set.range fun h => fun y => f (y * ι h)) := by
      rw [← hrange]; exact LinearMap.mem_range_self T u
    refine Submodule.span_induction (p := fun g _ => Continuous fun k : 𝐊 => g ((k : G)⁻¹)) ?_ ?_ ?_ ?_ hmem
    · rintro g ⟨h, rfl⟩
      have : (fun k : 𝐊 => (fun y => f (y * ι h)) ((k : G)⁻¹)) =
          (fun k : 𝐊 => conj (wf (k : G))) ∘ fun k => (⟨ι h, hιK h⟩ : 𝐊)⁻¹ * k := by
        funext k; simp only [hf, Function.comp_apply, mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [this]
      exact (Complex.continuous_conj.comp hwc).comp (continuous_const.mul continuous_id)
    · exact continuous_const
    · intro u v _ _ hu hv
      exact hu.fun_add hv
    · intro a u _ hu
      simpa only [Pi.smul_apply, smul_eq_mul] using continuous_const.fun_mul hu

  set A : (G → ℂ) → (G → ℂ) := fun g x => ∫ k, c * g ((k : G)⁻¹) * φ (x * (k : G)) ∂(maximalCompactHaar K) with hA
  have hint : ∀ u x, Integrable (fun k : 𝐊 => c * (T u) ((k : G)⁻¹) * φ (x * (k : G))) (maximalCompactHaar K) :=
    fun u x => integrable_of_continuous K ((continuous_const.mul (hTcont u)).mul (hφk x))
  let T' : (Fin m → Fin n → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun u => A (T u)
      map_add' := fun u v => by
        funext x
        simp only [hA, map_add, Pi.add_apply, mul_add, add_mul]
        exact integral_add (hint u x) (hint v x)
      map_smul' := fun a u => by
        funext x
        simp only [hA, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext k; ring }
  have hT'apply : ∀ u, T' u = A (T u) := fun u => rfl

  have hT' : ∀ (h : rowIsometrySubgroup₀ w₁.Completion) (u : Fin m → Fin n → ℂ),
      T' (fun j => (ρc h).mulVec (u j)) = fun y => T' u (y * ι h) := by
    intro h u
    rw [hT'apply, hT'apply, hT h u]
    funext y
    simp only [hA]
    have h1 := MeasureTheory.integral_mul_left_eq_self (μ := maximalCompactHaar K)
      (fun k : 𝐊 => c * T u ((k : G)⁻¹) * φ (y * ι h * (k : G))) (⟨ι h, hιK h⟩⁻¹ : 𝐊)
    rw [← h1]
    congr 1
    funext k
    simp only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]

  have hcol : ∀ (j : Fin m) (v : Fin n → ℂ), T' (Pi.single j v) ∈ ⨆ i : Fin (tys.card w₁), typeSubmodule ι (tys.rep w₁ i).ρ := by
    intro j v
    let Tj : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) := T'.comp (LinearMap.single ℂ (fun _ : Fin m => Fin n → ℂ) j)
    have hTj : ∀ (h : rowIsometrySubgroup₀ w₁.Completion) (x : Fin n → ℂ),
        Tj ((ρc h).mulVec x) = fun y => Tj x (y * ι h) := by
      intro h x
      show T' (Pi.single j ((ρc h).mulVec x)) = fun y => T' (Pi.single j x) (y * ι h)
      rw [← hT' h]
      congr 1
      funext j'
      by_cases hj : j' = j
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    exact H1 Tj hTj v
  have hsum : T' x₀ = ∑ j, T' (Pi.single j (x₀ j)) := by
    rw [← map_sum]
    congr 1
    exact (Finset.univ_sum_single x₀).symm
  have hgoal : (fun x => ∫ k, c * conj (wf (k : G)) * φ (x * (k : G)) ∂(maximalCompactHaar K)) = T' x₀ := by
    rw [hT'apply, hx₀]
    funext x
    simp only [hA, hf, inv_inv]
  rw [hgoal, hsum]
  exact Submodule.sum_mem _ fun j _ => hcol j (x₀ j)

end CutTransport

end AVKProof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule.AVKProof"

open AVKProof in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ κ : ↥(adelicMaximalCompact K) → ℂ, Continuous κ ∧ (∀ k, κ k⁻¹ = conj (κ k)) ∧
      (∀ k : ↥(adelicMaximalCompact K), ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k) ∧

      (∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K,
          (∫ k', κ k' * φ (g * (k' : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
            ∫ k', κ k' * φ (g * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ → (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = φ) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        Continuous (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
        IsArchKFinite K (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) (g * u) = (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) g) ∧
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∈ archCutSubmodule K tysK) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        (fun g => ∫ k, κ k * (∫ k', κ k' * φ (g * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
          ∂(maximalCompactHaar K)) =
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by
  classical
  obtain ⟨E, hfd, hEc, hEsupp, hEtr, hEstar, hEfin, hEU, hEcut, hOrb⟩ :=
    AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne K ξK hξu N hN tysK
  haveI := hfd

  let L : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (Kp K → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun k : Kp K => ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K))
  let E' : Submodule ℂ (Kp K → ℂ) := E.map L
  have hKpdet : ∀ k : Kp K, ∀ w : InfinitePlace K, w.IsReal →
      ((archComponent K w (NumberField.AdelicLevel.glArch (𝓞 K) K ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    fun k => (mem_Kp_iff K k).mp k.2
  have hE'c : ∀ v ∈ E', Continuous v := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hEc u hu).comp continuous_subtype_val
  have hE'r : ∀ k : Kp K, ∀ v ∈ E', (fun x => v (x * k)) ∈ E' := by
    rintro k _ ⟨u, hu, rfl⟩
    exact ⟨_, (hEtr _ (k : adelicMaximalCompact K).2 (hKpdet k) u hu).2, rfl⟩
  have hE'l : ∀ k : Kp K, ∀ v ∈ E', (fun x => v (k * x)) ∈ E' := by
    rintro k _ ⟨u, hu, rfl⟩
    exact ⟨_, (hEtr _ (k : adelicMaximalCompact K).2 (hKpdet k) u hu).1, rfl⟩
  have hE's : ∀ v ∈ E', (fun x => conj (v x⁻¹)) ∈ E' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, hEstar u hu, rfl⟩
  obtain ⟨e, hec, heinv, hesymm, heconv, hefix⟩ :=
    AutomorphicForm.exists_continuous_convolution_idempotent_forall_integral_mul_apply_eq_of_finiteDimensional_of_star_mem
      (μp K) E' hE'c hE'r hE'l hE's
  obtain ⟨w, hwE, hwL⟩ := Submodule.mem_map.mp heinv
  have hw : ∀ k : Kp K, w ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K) = e k⁻¹ := fun k => congrFun hwL k
  have hw0 : ∀ k : adelicMaximalCompact K, k ∉ Kp K → w (k : AdelicGL2 (𝓞 K) K) = 0 := by
    intro k hk
    by_contra h
    exact hk ((mem_Kp_iff K k).mpr (hEsupp w hwE _ h).2)

  set m : ℝ≥0∞ := (maximalCompactHaar K) (Kp K : Set (adelicMaximalCompact K)) with hm
  have hm0 : m ≠ 0 := (isOpen_Kp K).measure_ne_zero (maximalCompactHaar K) ⟨1, (Kp K).one_mem⟩
  have hmt : m ≠ ⊤ := measure_ne_top _ _
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hm0 hmt
  set c : ℝ := m.toReal⁻¹ with hc
  have hmc : m.toReal * c = 1 := mul_inv_cancel₀ hmpos.ne'

  set κ : adelicMaximalCompact K → ℂ := fun k => (c : ℂ) * conj (w (k : AdelicGL2 (𝓞 K) K)) with hκ
  have hκKp : ∀ k : Kp K, κ (k : adelicMaximalCompact K) = (c : ℂ) * e k := by
    intro k
    simp only [hκ, hw k, hesymm k, Complex.conj_conj]
  have hκ0 : ∀ k : adelicMaximalCompact K, k ∉ Kp K → κ k = 0 := by
    intro k hk
    simp only [hκ, hw0 k hk, map_zero, mul_zero]
  have hκc : Continuous κ := continuous_const.mul (Complex.continuous_conj.comp (hEc w hwE))

  have hwU : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ y : AdelicGL2 (𝓞 K) K,
      w (u⁻¹ * y) = w y := by
    intro u hu y
    have h := hEU _ (hEstar w hwE) y⁻¹ u hu
    simp only [mul_inv_rev, inv_inv] at h
    have h' := congrArg conj h
    simpa using h'
  have hsymm : ∀ k, κ k⁻¹ = conj (κ k) := by
    intro k
    by_cases hk : k ∈ Kp K
    · obtain ⟨k', rfl⟩ : ∃ k' : Kp K, (k' : adelicMaximalCompact K) = k := ⟨⟨k, hk⟩, rfl⟩
      rw [show (k' : adelicMaximalCompact K)⁻¹ = ((k'⁻¹ : Kp K) : adelicMaximalCompact K) from rfl, hκKp, hκKp,
        map_mul, Complex.conj_ofReal, hesymm]
    · have hk' : k⁻¹ ∉ Kp K := fun h => hk (by simpa using (Kp K).inv_mem h)
      rw [hκ0 _ hk', hκ0 _ hk, map_zero]
  have hconv : ∀ k, ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k := by
    intro k
    rw [integral_eq_of_support K _ (fun k' hk' => by rw [hκ0 _ hk', zero_mul])]
    by_cases hk : k ∈ Kp K
    · obtain ⟨k₀, rfl⟩ : ∃ k₀ : Kp K, (k₀ : adelicMaximalCompact K) = k := ⟨⟨k, hk⟩, rfl⟩
      have h1 : ∀ k' : Kp K, κ (k' : adelicMaximalCompact K) * κ ((k' : adelicMaximalCompact K)⁻¹ * k₀) =
          (c : ℂ) * ((c : ℂ) * (e k' * e (k'⁻¹ * k₀))) := by
        intro k'
        rw [hκKp, show (k' : adelicMaximalCompact K)⁻¹ * (k₀ : adelicMaximalCompact K) =
          ((k'⁻¹ * k₀ : Kp K) : adelicMaximalCompact K) from rfl, hκKp]
        ring
      simp_rw [h1]
      rw [integral_const_mul, integral_const_mul, heconv k₀, hκKp, ← mul_assoc, ← mul_assoc,
        ← Complex.ofReal_mul, hmc, Complex.ofReal_one, one_mul]
    · have h1 : ∀ k' : Kp K, κ (k' : adelicMaximalCompact K) * κ ((k' : adelicMaximalCompact K)⁻¹ * k) = 0 := by
        intro k'
        have : (k' : adelicMaximalCompact K)⁻¹ * k ∉ Kp K := fun h => hk (by
          simpa using (Kp K).mul_mem (k' : Kp K).2 h)
        rw [hκ0 _ this, mul_zero]
      simp_rw [h1]
      rw [integral_zero, mul_zero, hκ0 _ hk]
  have heconj : ∀ k₀ x : Kp K, e (k₀ * x * k₀⁻¹) = e x :=
    unit_conj_eq E' e hE'r hE'l hE's heinv hesymm hefix
  have hκconj : ∀ (k₀ : Kp K) (k : adelicMaximalCompact K),
      κ ((k₀ : adelicMaximalCompact K) * k * (k₀ : adelicMaximalCompact K)⁻¹) = κ k := by
    intro k₀ k
    by_cases hk : k ∈ Kp K
    · obtain ⟨k', rfl⟩ : ∃ k' : Kp K, (k' : adelicMaximalCompact K) = k := ⟨⟨k, hk⟩, rfl⟩
      rw [show (k₀ : adelicMaximalCompact K) * k' * (k₀ : adelicMaximalCompact K)⁻¹ =
        ((k₀ * k' * k₀⁻¹ : Kp K) : adelicMaximalCompact K) from rfl, hκKp, hκKp, heconj]
    · have : (k₀ : adelicMaximalCompact K) * k * (k₀ : adelicMaximalCompact K)⁻¹ ∉ Kp K := by
        intro h
        apply hk
        have := (Kp K).mul_mem ((Kp K).mul_mem ((Kp K).inv_mem k₀.2) h) k₀.2
        simpa [mul_assoc] using this
      rw [hκ0 _ this, hκ0 _ hk]
  refine ⟨κ, hκc, hsymm, hconv, fun φ k hk g => integral_comm_of_conj hκconj φ k ((mem_Kp_iff K k).mpr hk) g,
    ?_, ?_, ?_⟩
  ·
    intro φ hφc hφK hφU hφcut hφZ
    funext g
    obtain ⟨v, hvE, hv⟩ := hOrb φ hφc hφK hφU hφcut hφZ g
    rw [integral_eq_of_support K _ (fun k' hk' => by rw [hκ0 _ hk', zero_mul])]
    have h1 : ∀ k' : Kp K, κ (k' : adelicMaximalCompact K) * φ (g * ((k' : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)) =
        (c : ℂ) * (e k' * (L v) (1 * k')) := by
      intro k'
      rw [hκKp, one_mul, mul_assoc]
      congr 2
      exact (hv _ (k' : adelicMaximalCompact K).2 (hKpdet k')).symm
    simp_rw [h1]
    rw [integral_const_mul, hefix (L v) ⟨v, hvE, rfl⟩ 1, ← mul_assoc, ← Complex.ofReal_mul, hmc,
      Complex.ofReal_one, one_mul]
    show v (((1 : Kp K) : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K) = φ g
    rw [hv _ ((1 : Kp K) : adelicMaximalCompact K).2 (hKpdet 1)]
    show φ (g * 1) = φ g
    rw [mul_one]
  ·
    intro φ hφc hφK
    refine ⟨continuous_average hκc hφc, ?_, ?_, ?_⟩
    ·
      intro w'
      classical
      obtain ⟨S, hSc, hS⟩ := hEfin w hwE
      refine ⟨S.image fun s x => ∫ k, (c : ℂ) * conj (s (k : AdelicGL2 (𝓞 K) K)) * φ (x * (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K), fun k₀ hk₀ => ?_⟩
      have hk₀K : k₀ ∈ adelicMaximalCompact K := archRowIsometrySubgroup_le K w' hk₀
      have hmem := average_mem_span hφc (c : ℂ) S hSc _ (hS _ ((adelicMaximalCompact K).inv_mem hk₀K))
      have heq : (fun x => ∫ k, κ k * φ (x * k₀ * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
          fun x => ∫ k, (c : ℂ) * conj ((fun y => w (((⟨k₀, hk₀K⟩ : adelicMaximalCompact K)⁻¹ : AdelicGL2 (𝓞 K) K) * y))
            (k : AdelicGL2 (𝓞 K) K)) * φ (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
        funext x
        rw [show x * k₀ = x * ((⟨k₀, hk₀K⟩ : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K) from rfl, average_translate]
        simp only [hκ, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq]
      exact hmem
    ·
      intro g u hu
      show (∫ k, κ k * φ (g * u * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
        ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
      have huK : u ∈ adelicMaximalCompact K := level_le K N hu
      rw [show g * u = g * ((⟨u, huK⟩ : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K) from rfl, average_translate]
      congr 1
      funext k
      simp only [hκ, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hwU u hu]
    ·
      have hwc : Continuous fun k : adelicMaximalCompact K => w (k : AdelicGL2 (𝓞 K) K) := hEc w hwE
      have hw0' : ∀ y : AdelicGL2 (𝓞 K) K, y ∉ adelicMaximalCompact K → w y = 0 := by
        intro y hy
        by_contra h
        exact hy (hEsupp w hwE y h).1
      have hcut : (fun y => conj (w y⁻¹)) ∈ archCutSubmodule K tysK := hEcut (hEstar w hwE)
      have := average_mem_archCutSubmodule tysK hwc hw0' hcut (c : ℂ) hφc
      simpa only [hκ] using this
  ·
    intro φ hφc hφK
    funext g
    exact average_average_eq hκc hconv hφc g

end
end S_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule (solution)
