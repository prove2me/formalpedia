-- Prove2me | solution 1 for AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/bed72059-4519-598b-b03d-96c525f7cc55

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

section

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped Classical NumberField

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

private def seqLimitOrZero (s : ℕ → ℂ) : ℂ :=
  if ∃ L : ℂ, Tendsto s atTop (𝓝 L) then limUnder atTop s else 0

private theorem seqLimitOrZero_eq_of_tendsto {s : ℕ → ℂ} {L : ℂ} (h : Tendsto s atTop (𝓝 L)) :
    seqLimitOrZero s = L := by
  rw [seqLimitOrZero, if_pos ⟨L, h⟩]
  exact h.limUnder_eq

private theorem seqLimitOrZero_const_mul (c : ℂ) (hc : c ≠ 0) (s : ℕ → ℂ) :
    seqLimitOrZero (fun n => c * s n) = c * seqLimitOrZero s := by
  by_cases h : ∃ L : ℂ, Tendsto s atTop (𝓝 L)
  · obtain ⟨L, hL⟩ := h
    rw [seqLimitOrZero_eq_of_tendsto hL, seqLimitOrZero_eq_of_tendsto (hL.const_mul c)]
  · have h' : ¬ ∃ L : ℂ, Tendsto (fun n => c * s n) atTop (𝓝 L) := by
      rintro ⟨L, hL⟩
      refine h ⟨c⁻¹ * L, ?_⟩
      have := hL.const_mul c⁻¹
      simpa [inv_mul_cancel_left₀ hc] using this
    simp only [seqLimitOrZero, if_neg h, if_neg h', mul_zero]

variable (F : Type) [Field F] [NumberField F]

private theorem isAutomorphicFnAt_iff_isLsXiFunction_and_memLp (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsAutomorphicFnAt F pins ξ φ ↔
      letI := pins.mS
      IsLsXiFunction (𝓞 F) F pins.Z ξ φ ∧ MemLp φ 2 (pins.μ.restrict pins.D) := by
  letI := pins.mS
  exact lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ

private theorem exists_isAutomorphicFnAt_of_ae_tendsto (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (u : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (hu : ∀ n, IsAutomorphicFnAt F pins ξ (u n))
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : letI := pins.mS; MemLp v 2 (pins.μ.restrict pins.D))
    (hlim : letI := pins.mS;
      ∀ᵐ g ∂(pins.μ.restrict pins.D), Tendsto (fun n => u n g) atTop (𝓝 (v g))) :
    ∃ U : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ U ∧
      (letI := pins.mS; U =ᵐ[pins.μ.restrict pins.D] v) := by
  letI := pins.mS
  have hu' : ∀ n, IsLsXiFunction (𝓞 F) F pins.Z ξ (u n) := fun n =>
    ((isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ (u n)).1 (hu n)).1
  set U : AdelicGL2 (𝓞 F) F → ℂ := fun g => seqLimitOrZero (fun n => u n g) with hUdef
  have hUv : U =ᵐ[pins.μ.restrict pins.D] v :=
    hlim.mono fun g hg => seqLimitOrZero_eq_of_tendsto hg
  refine ⟨U, (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ U).2 ⟨⟨?_, ?_⟩, ?_⟩, hUv⟩
  · intro γ g
    simp only [hUdef]
    congr 1
    funext n
    exact (hu' n).left_invariant γ g
  · intro z g
    simp only [hUdef]
    have hz : ((ξ z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero (ξ z)
    rw [← seqLimitOrZero_const_mul _ hz]
    congr 1
    funext n
    exact (hu' n).central_transform z g
  · exact hv.ae_eq hUv.symm

private theorem exists_isAutomorphicFnAt_of_tendsto_eLpNorm (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (u : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (hu : ∀ n, IsAutomorphicFnAt F pins ξ (u n))
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : letI := pins.mS; MemLp v 2 (pins.μ.restrict pins.D))
    (hconv : letI := pins.mS;
      Tendsto (fun n => eLpNorm (u n - v) 2 (pins.μ.restrict pins.D)) atTop (𝓝 0)) :
    ∃ U : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ U ∧
      (letI := pins.mS; U =ᵐ[pins.μ.restrict pins.D] v) := by
  letI := pins.mS
  have hmeas : ∀ n, AEStronglyMeasurable (u n) (pins.μ.restrict pins.D) := fun n =>
    ((isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ (u n)).1 (hu n)).2.1
  have hinm : TendstoInMeasure (pins.μ.restrict pins.D) u atTop v :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hmeas hv.1 hconv
  obtain ⟨ns, -, hae⟩ := hinm.exists_seq_tendsto_ae
  exact exists_isAutomorphicFnAt_of_ae_tendsto F pins ξ (fun i => u (ns i)) (fun i => hu (ns i))
    v hv hae

section Algebra

variable {F}

namespace IsAutomorphicFnAt
private theorem _root_.AutomorphicForm.IsAutomorphicFnAt.add {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsAutomorphicFnAt F pins ξ φ)
    (hψ : IsAutomorphicFnAt F pins ξ ψ) : IsAutomorphicFnAt F pins ξ (φ + ψ) := by
  letI := pins.mS
  obtain ⟨hφ₁, hφ₂⟩ := (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ φ).1 hφ
  obtain ⟨hψ₁, hψ₂⟩ := (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ ψ).1 hψ
  refine (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ (φ + ψ)).2 ⟨⟨?_, ?_⟩, hφ₂.add hψ₂⟩
  · intro γ g
    simp only [Pi.add_apply, hφ₁.left_invariant γ g, hψ₁.left_invariant γ g]
  · intro z g
    simp only [Pi.add_apply, hφ₁.central_transform z g, hψ₁.central_transform z g, mul_add]

end IsAutomorphicFnAt
p2m_export "AutomorphicForm" "IsAutomorphicFnAt.add"
namespace IsAutomorphicFnAt
private theorem _root_.AutomorphicForm.IsAutomorphicFnAt.const_smul {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsAutomorphicFnAt F pins ξ φ) (c : ℂ) :
    IsAutomorphicFnAt F pins ξ (c • φ) := by
  letI := pins.mS
  obtain ⟨hφ₁, hφ₂⟩ := (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ φ).1 hφ
  refine (isAutomorphicFnAt_iff_isLsXiFunction_and_memLp F pins ξ (c • φ)).2
    ⟨⟨?_, ?_⟩, hφ₂.const_smul c⟩
  · intro γ g
    simp only [Pi.smul_apply, hφ₁.left_invariant γ g]
  · intro z g
    simp only [Pi.smul_apply, hφ₁.central_transform z g, smul_eq_mul]
    ring

end IsAutomorphicFnAt
p2m_export "AutomorphicForm" "IsAutomorphicFnAt.const_smul"
namespace IsAutomorphicFnAt
private theorem _root_.AutomorphicForm.IsAutomorphicFnAt.neg {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsAutomorphicFnAt F pins ξ φ) :
    IsAutomorphicFnAt F pins ξ (-φ) := by
  simpa [neg_one_smul] using hφ.const_smul (-1 : ℂ)

end IsAutomorphicFnAt
p2m_export "AutomorphicForm" "IsAutomorphicFnAt.neg"
namespace IsAutomorphicFnAt
private theorem _root_.AutomorphicForm.IsAutomorphicFnAt.sub {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsAutomorphicFnAt F pins ξ φ)
    (hψ : IsAutomorphicFnAt F pins ξ ψ) : IsAutomorphicFnAt F pins ξ (φ - ψ) := by
  simpa [sub_eq_add_neg] using hφ.add hψ.neg

end IsAutomorphicFnAt
p2m_export "AutomorphicForm" "IsAutomorphicFnAt.sub"
end Algebra

end AutomorphicForm

end

end

section

set_option autoImplicit false

open NumberField Matrix Topology
open scoped Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem exists_isOpen_zero_mem_algebraMap_mem_imp_eq_zero :
    ∃ O : Set (AdeleRing (𝓞 F) F), IsOpen O ∧ (0 : AdeleRing (𝓞 F) F) ∈ O ∧
      ∀ k : F, algebraMap F (AdeleRing (𝓞 F) F) k ∈ O → k = 0 := by
  obtain ⟨U, hUo, ⟨u₀, hu₀⟩, hUsub⟩ := NumberField.AdelicBox.exists_isOpen_subset_adelicBox F
  refine ⟨(fun x => x + u₀) ⁻¹' U, hUo.preimage (continuous_id.add continuous_const), ?_, ?_⟩
  · show (0 : AdeleRing (𝓞 F) F) + u₀ ∈ U
    simpa using hu₀
  · intro k hk
    obtain ⟨k', -, huniq⟩ := NumberField.AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F u₀
    have h1 : k = k' := huniq k (hUsub hk)
    have h2 : (0 : F) = k' := huniq 0 (by simpa using hUsub hu₀)
    rw [h1, ← h2]

private theorem exists_isOpen_one_mem_globalPoints_mem_imp_eq_one :
    ∃ N : Set (AdelicGL2 (𝓞 F) F), IsOpen N ∧ (1 : AdelicGL2 (𝓞 F) F) ∈ N ∧
      ∀ γ : Matrix.GeneralLinearGroup (Fin 2) F, globalPoints (𝓞 F) F γ ∈ N → γ = 1 := by
  obtain ⟨O, hOo, hO0, hO⟩ := exists_isOpen_zero_mem_algebraMap_mem_imp_eq_zero F
  refine ⟨{x : AdelicGL2 (𝓞 F) F | ∀ i j, (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j ∈ O}, ?_, ?_, ?_⟩
  · simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOo.preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  · intro i j
    simpa using hO0
  · intro γ hγ
    ext i j
    have h := hγ i j
    have hentry : ((globalPoints (𝓞 F) F γ : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
        = algebraMap F (AdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j) := by
      simp only [globalPoints]
      exact Matrix.GeneralLinearGroup.map_apply _ i j γ
    have hone : (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
        = algebraMap F (AdeleRing (𝓞 F) F) ((1 : Matrix (Fin 2) (Fin 2) F) i j) := by
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    rw [hentry, hone, ← map_sub] at h
    have h0 := sub_eq_zero.mp (hO _ h)
    simpa using h0

private theorem discreteTopology_range_globalPoints :
    DiscreteTopology ((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) := by
  obtain ⟨N, hNo, hN1, hN⟩ := exists_isOpen_one_mem_globalPoints_mem_imp_eq_one F
  rw [discreteTopology_iff_isOpen_singleton_one]
  have hset : ({1} : Set ((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)))
      = Subtype.val ⁻¹' N := by
    ext ⟨h, hh⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h1
      have h1' : h = 1 := by simpa using congrArg Subtype.val h1
      rw [h1']
      exact hN1
    · intro hmem
      obtain ⟨γ, rfl⟩ := hh
      have hγ : γ = 1 := hN γ hmem
      subst hγ
      ext
      simp
  rw [hset]
  exact hNo.preimage continuous_subtype_val

private theorem isClosed_range_globalPoints :
    IsClosed (((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  haveI := discreteTopology_range_globalPoints F
  exact Subgroup.isClosed_of_discrete

private theorem finite_inter_range_globalPoints_of_isCompact {C : Set (AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) :
    (C ∩ (((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F))).Finite := by
  haveI := discreteTopology_range_globalPoints F
  have hdisc : IsDiscrete (((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) :=
    SetLike.isDiscrete_iff_discreteTopology.2 inferInstance
  have hdisc' : IsDiscrete (C ∩ (((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F))) :=
    isDiscrete_iff_discreteTopology.2
      (DiscreteTopology.of_subset (isDiscrete_iff_discreteTopology.1 hdisc) Set.inter_subset_right)
  exact (hC.inter_right (isClosed_range_globalPoints F)).finite hdisc'

private theorem exists_encard_globalPoints_mul_mem_le_of_isCompact (C : Set (AdelicGL2 (𝓞 F) F))
    (hC : IsCompact C) :
    ∃ m : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      {γ : (globalPoints (𝓞 F) F).range | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m := by
  have hK : IsCompact (C * C⁻¹) := hC.mul hC.inv
  have hfin := finite_inter_range_globalPoints_of_isCompact F hK
  have hT : ({δ : (globalPoints (𝓞 F) F).range | (δ : AdelicGL2 (𝓞 F) F) ∈ C * C⁻¹}).Finite := by
    have hEq : ({δ : (globalPoints (𝓞 F) F).range | (δ : AdelicGL2 (𝓞 F) F) ∈ C * C⁻¹})
        = Subtype.val ⁻¹' (C * C⁻¹ ∩ (((globalPoints (𝓞 F) F).range :
            Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
      ext δ
      simp
    rw [hEq]
    exact hfin.preimage Subtype.val_injective.injOn
  obtain ⟨m, hm⟩ := hT.exists_encard_eq_coe
  refine ⟨m, fun g => ?_⟩
  rw [← hm]
  by_cases hne : ({γ : (globalPoints (𝓞 F) F).range | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}).Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    refine Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_
      (mul_left_injective γ₀⁻¹).injOn
    intro γ hγ
    have hmem : ((γ : AdelicGL2 (𝓞 F) F) * g) * ((γ₀ : AdelicGL2 (𝓞 F) F) * g)⁻¹ ∈ C * C⁻¹ :=
      Set.mul_mem_mul hγ (Set.inv_mem_inv.2 hγ₀)
    show ((γ * γ₀⁻¹ : (globalPoints (𝓞 F) F).range) : AdelicGL2 (𝓞 F) F) ∈ C * C⁻¹
    convert hmem using 1
    simp [mul_assoc]
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.encard_empty]
    exact zero_le

private theorem countable_of_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem countable_range_globalPoints :
    Countable ((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) := by
  haveI : Countable F := countable_of_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have hinj : Function.Injective
      (Units.val : (Matrix (Fin 2) (Fin 2) F)ˣ → Matrix (Fin 2) (Fin 2) F) := fun _ _ h => Units.ext h
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := hinj.countable
  exact (Set.countable_range (globalPoints (𝓞 F) F)).to_subtype

end AutomorphicForm

end

end

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab.AutomorphicForm"
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
namespace LsXiOrthogonalSplit
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private abbrev slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

private abbrev slabHaar (d₁ d₂ : ℝ) : Measure (AdelicGL2 (𝓞 F) F) :=
  (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)

private abbrev pins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range

private abbrev shear : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
  fun p => unipotentGL2 p.1 * p.2

private theorem central_transform_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) (z : (pins F Φ).Z)
    (g : AdelicGL2 (𝓞 F) F) :
    u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).1.central_transform z g

private theorem left_invariant_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) (γ : Γ F)
    (g : AdelicGL2 (𝓞 F) F) : u ((γ : AdelicGL2 (𝓞 F) F) * g) = u g := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  have h := ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).1.left_invariant γ₀ g
  rwa [hγ₀] at h

private theorem memLp_restrict_Φ_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).mp hu).2

private theorem det_unipotentGL2_mul (q : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 q * g) = Matrix.GeneralLinearGroup.det g := by
  have h1 : Matrix.GeneralLinearGroup.det (unipotentGL2 (R := AdeleRing (𝓞 F) F) q) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  rw [map_mul, h1, one_mul]

private theorem preimage_unipotentGL2_mul_slab (d₁ d₂ : ℝ) (q : AdeleRing (𝓞 F) F) :
    (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) ⁻¹' slab F d₁ d₂ = slab F d₁ d₂ := by
  ext g
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) ∈ Set.Icc d₁ d₂
    ↔ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂
  rw [det_unipotentGL2_mul]

private theorem measurePreserving_unipotentGL2_mul_slabHaar (d₁ d₂ : ℝ) (q : AdeleRing (𝓞 F) F) :
    MeasurePreserving (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) (slabHaar F d₁ d₂) (slabHaar F d₁ d₂) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hmeas : Measurable (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) := measurable_const_mul _
  refine ⟨hmeas, ?_⟩
  ext t ht
  rw [Measure.map_apply hmeas ht, Measure.restrict_apply (hmeas ht), Measure.restrict_apply ht]
  conv_lhs => rw [← preimage_unipotentGL2_mul_slab F d₁ d₂ q, ← Set.preimage_inter]
  exact measure_preimage_mul _ _ _

private theorem shear_mem_slab (d₁ d₂ : ℝ) (q : AdeleRing (𝓞 F) F) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ slab F d₁ d₂) : unipotentGL2 q * g ∈ slab F d₁ d₂ := by
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (unipotentGL2 q * g)) ∈ Set.Icc d₁ d₂
  rw [det_unipotentGL2_mul]
  exact hg

private theorem setLIntegral_le_mul_setLIntegral_of_invariant
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : MeasurableSet C)
    (m : ℕ) (hm : ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (φ : AdelicGL2 (𝓞 F) F → ENNReal) (hφ : AEMeasurable φ (slabHaar F d₁ d₂))
    (hφinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), φ ((γ : AdelicGL2 (𝓞 F) F) * g) = φ g) :
    ∫⁻ g in C, φ g ∂(slabHaar F d₁ d₂) ≤ (m : ENNReal) * ∫⁻ g in Φ, φ g ∂(slabHaar F d₁ d₂) := by
  classical

  have hkey : ∀ γ : Γ F,
      ∫⁻ x in C ∩ γ • Φ, φ x ∂(slabHaar F d₁ d₂)
        = ∫⁻ y in Φ, C.indicator φ ((γ : AdelicGL2 (𝓞 F) F) * y) ∂(slabHaar F d₁ d₂) := by
    intro γ
    have h1 := (measurePreserving_smul γ (slabHaar F d₁ d₂)).setLIntegral_comp_emb
      (measurableEmbedding_const_smul γ) (C.indicator φ) Φ
    rw [Set.image_smul, lintegral_indicator hC, Measure.restrict_restrict hC] at h1
    exact h1.symm
  have hmeas : ∀ γ : Γ F, AEMeasurable (fun y => C.indicator φ ((γ : AdelicGL2 (𝓞 F) F) * y))
      ((slabHaar F d₁ d₂).restrict Φ) :=
    fun γ => (AEMeasurable.comp_quasiMeasurePreserving (hφ.indicator hC)
      (measurePreserving_smul γ (slabHaar F d₁ d₂)).quasiMeasurePreserving).mono_measure Measure.restrict_le_self
  have h2 := lintegral_tsum hmeas
  rw [hΦ.setLIntegral_eq_tsum φ C]
  simp_rw [hkey]
  refine h2.symm.trans_le ?_
  rw [← lintegral_const_mul' (m : ENNReal) φ (ENNReal.natCast_ne_top m)]
  refine lintegral_mono fun y => ?_

  have hpt : ∀ γ : Γ F, C.indicator φ ((γ : AdelicGL2 (𝓞 F) F) * y)
      = {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C}.indicator (fun _ => φ y) γ := by
    intro γ
    by_cases hγ : (γ : AdelicGL2 (𝓞 F) F) * y ∈ C
    · have hγ' : γ ∈ {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C} := hγ
      simp only [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ', hφinv γ y]
    · have hγ' : γ ∉ {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C} := hγ
      simp only [Set.indicator_apply, hγ, hγ', if_false]
  simp_rw [hpt]
  rw [← tsum_subtype, ENNReal.tsum_set_const]
  calc ({γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * y ∈ C}.encard : ENNReal) * φ y
      ≤ ((m : ENat) : ENNReal) * φ y := by
        gcongr
        exact_mod_cast hm y
    _ = (m : ENNReal) * φ y := by simp

private theorem quasiMeasurePreserving_shear_prod (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hshear : Measurable (shear F)) (ρ : Measure (AdelicGL2 (𝓞 F) F)) [SFinite ρ]
    (hρ : ρ ≤ slabHaar F d₁ d₂) :
    Measure.QuasiMeasurePreserving
      (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) (ρ.prod (pins F Φ).ν)
      (slabHaar F d₁ d₂) := by
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  have hmeas' := hshear.comp measurable_swap
  have hmeas : Measurable (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) := hmeas'
  refine ⟨hmeas, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
  have hsec : ∀ q : AdeleRing (𝓞 F) F,
      ρ ((fun g : AdelicGL2 (𝓞 F) F => (g, q)) ⁻¹'
        ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N)) = 0 := by
    intro q
    refine nonpos_iff_eq_zero.mp ?_
    calc ρ ((fun g : AdelicGL2 (𝓞 F) F => (g, q)) ⁻¹'
            ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N))
        ≤ slabHaar F d₁ d₂ ((fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) ⁻¹' N) := Measure.le_iff'.mp hρ _
      _ = slabHaar F d₁ d₂ N :=
          (measurePreserving_unipotentGL2_mul_slabHaar F d₁ d₂ q).measure_preimage hN.nullMeasurableSet
      _ = 0 := hN0
  calc (ρ.prod (pins F Φ).ν).map (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) N
      = ρ.prod (pins F Φ).ν
          ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N) :=
        Measure.map_apply hmeas hN
    _ = ∫⁻ q, ρ ((fun g : AdelicGL2 (𝓞 F) F => (g, q)) ⁻¹'
          ((fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => unipotentGL2 p.2 * p.1) ⁻¹' N))
            ∂(pins F Φ).ν :=
        Measure.prod_apply_symm (hmeas hN)
    _ = 0 := by simp only [hsec, lintegral_zero]

private theorem setLIntegral_lintegral_shear_le
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (K K' : Set (AdelicGL2 (𝓞 F) F)) (hK : MeasurableSet K) (hK' : IsCompact K') (hKK' : K ⊆ K')
    (Kb : Set (AdeleRing (𝓞 F) F)) (_hKb : IsCompact Kb) (hbox : adelicBox F ⊆ Kb)
    (φ : AdelicGL2 (𝓞 F) F → ENNReal) (hφ : AEMeasurable φ (slabHaar F d₁ d₂)) :
    (∫⁻ g in K, (∫⁻ q, φ (unipotentGL2 q * g) ∂(pins F Φ).ν) ∂(slabHaar F d₁ d₂))
      ≤ ∫⁻ g in shear F '' (Kb ×ˢ K'), φ g ∂(slabHaar F d₁ d₂) := by
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  haveI : IsFiniteMeasure ((slabHaar F d₁ d₂).restrict K) := by
    haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.restrict_apply hK]
    exact lt_of_le_of_lt (measure_mono (Set.inter_subset_left.trans hKK')) hK'.measure_lt_top

  have hq : ∀ q ∈ adelicBox F,
      ∫⁻ g in K, φ (unipotentGL2 q * g) ∂(slabHaar F d₁ d₂)
        ≤ ∫⁻ g in shear F '' (Kb ×ˢ K'), φ g ∂(slabHaar F d₁ d₂) := by
    intro q hqb
    haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
    have hemb : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 F) F => unipotentGL2 q * g) :=
      (MeasurableEquiv.mulLeft (unipotentGL2 q)).measurableEmbedding
    refine ((measurePreserving_unipotentGL2_mul_slabHaar F d₁ d₂ q).setLIntegral_comp_emb hemb φ K).trans_le ?_
    refine lintegral_mono_set ?_
    rintro _ ⟨g, hgK, rfl⟩
    exact ⟨(q, g), Set.mk_mem_prod (hbox hqb) (hKK' hgK), rfl⟩
  have hae : ∀ᵐ q ∂(pins F Φ).ν, q ∈ adelicBox F := by
    show ∀ᵐ q ∂(((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • (adelicAddHaar (𝓞 F) F).restrict (adelicBox F)),
      q ∈ adelicBox F
    exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_adelicBox F)) _
  have hswap := lintegral_lintegral_swap (μ := (slabHaar F d₁ d₂).restrict K) (ν := (pins F Φ).ν)
    (f := fun g q => φ (unipotentGL2 q * g))
    (hφ.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_shear_prod F d₁ d₂ Φ hshear _ Measure.restrict_le_self))
  refine hswap.trans_le ?_
  calc ∫⁻ q, ∫⁻ g in K, φ (unipotentGL2 q * g) ∂(slabHaar F d₁ d₂) ∂(pins F Φ).ν
      ≤ ∫⁻ _q, ∫⁻ g in shear F '' (Kb ×ˢ K'), φ g ∂(slabHaar F d₁ d₂) ∂(pins F Φ).ν :=
        lintegral_mono_ae (hae.mono fun q hqb => hq q hqb)
    _ = ∫⁻ g in shear F '' (Kb ×ˢ K'), φ g ∂(slabHaar F d₁ d₂) := by
        rw [lintegral_const, measure_univ, mul_one]

private theorem aestronglyMeasurable_slabHaar_of_invariant (a b : ℝ) (Φ' : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b)]
    (hΦ' : IsFundamentalDomain (Γ F) Φ' (slabHaar F a b)) (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), u ((γ : AdelicGL2 (𝓞 F) F) * g) = u g)
    (hu : AEStronglyMeasurable u ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ')) :
    AEStronglyMeasurable u (slabHaar F a b) := by
  have hΦ'' : AEStronglyMeasurable u ((slabHaar F a b).restrict Φ') :=
    hu.mono_measure (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
  rw [← hΦ'.sum_restrict, aestronglyMeasurable_sum_measure_iff]
  intro γ
  have hmp := (measurePreserving_smul γ (slabHaar F a b)).restrict_image_emb (measurableEmbedding_const_smul γ) Φ'
  rw [Set.image_smul] at hmp
  rw [← hmp.map_eq, (measurableEmbedding_const_smul γ).aestronglyMeasurable_map_iff]
  have hcomp : (u ∘ fun x : AdelicGL2 (𝓞 F) F => γ • x) = u := funext fun x => hinv γ x
  rw [hcomp]
  exact hΦ''

private theorem aestronglyMeasurable_slabHaar_of_isAutomorphicFnAt
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    AEStronglyMeasurable u (slabHaar F d₁ d₂) := by
  exact aestronglyMeasurable_slabHaar_of_invariant F d₁ d₂ Φ hΦ u (left_invariant_of_isAutomorphicFnAt F Φ ξ hu)
    (memLp_restrict_Φ_of_isAutomorphicFnAt F Φ ξ hu).1

private theorem aestronglyMeasurable_comp_shear_prod
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F)) (hshear : Measurable (shear F))
    (ρ : Measure (AdelicGL2 (𝓞 F) F)) [SFinite ρ] (hρ : ρ ≤ slabHaar F d₁ d₂)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : AEStronglyMeasurable u (slabHaar F d₁ d₂)) :
    AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => u (unipotentGL2 p.2 * p.1))
      (ρ.prod (pins F Φ).ν) :=
  hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_shear_prod F d₁ d₂ Φ hshear ρ hρ)

private theorem aestronglyMeasurable_constantTerm
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂)) (hshear : Measurable (shear F))
    (ρ : Measure (AdelicGL2 (𝓞 F) F)) [SFinite ρ] (hρ : ρ ≤ slabHaar F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    AEStronglyMeasurable (fun g => constantTerm (pins F Φ).ν unipotentGL2 u g) ρ := by
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  exact (aestronglyMeasurable_comp_shear_prod F d₁ d₂ Φ hshear ρ hρ u
    (aestronglyMeasurable_slabHaar_of_isAutomorphicFnAt F d₁ d₂ Φ hΦ ξ u hu)).integral_prod_right'

private theorem enorm_integral_sq_le_lintegral_enorm_sq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : α → ℂ) (hf : AEStronglyMeasurable f ν) :
    ‖∫ x, f x ∂ν‖ₑ ^ 2 ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have h1 : ‖∫ x, f x ∂ν‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm f
  have h2 : ∫⁻ x, ‖f x‖ₑ ∂ν ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf.enorm
      (aemeasurable_const (b := (1 : ENNReal)))
    simpa [measure_univ] using h
  calc ‖∫ x, f x ∂ν‖ₑ ^ 2
      ≤ ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr; exact h1.trans h2
    _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
        simp only [ENNReal.rpow_ofNat]

private theorem ae_integrable_and_setLIntegral_constantTerm_sq_le
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q)
    (K K' : Set (AdelicGL2 (𝓞 F) F)) (hK : MeasurableSet K) (hK' : IsCompact K') (hKK' : K ⊆ K')
    (Kb : Set (AdeleRing (𝓞 F) F)) (hKb : IsCompact Kb) (hbox : adelicBox F ⊆ Kb)
    (m : ℕ)
    (hm : ∀ g : AdelicGL2 (𝓞 F) F,
      {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ shear F '' (Kb ×ˢ K')}.encard ≤ m)
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    (∀ᵐ g ∂((slabHaar F d₁ d₂).restrict K),
        Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν)
    ∧ (∫⁻ g in K, ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂))
        ≤ (m : ENNReal) * ∫⁻ g in Φ, ‖u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂) := by
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : IsFiniteMeasure ((slabHaar F d₁ d₂).restrict K) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.restrict_apply hK]
    exact lt_of_le_of_lt (measure_mono (Set.inter_subset_left.trans hKK')) hK'.measure_lt_top
  have huK : AEStronglyMeasurable u (slabHaar F d₁ d₂) :=
    aestronglyMeasurable_slabHaar_of_isAutomorphicFnAt F d₁ d₂ Φ hΦ ξ u hu
  have hF : AEStronglyMeasurable
      (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => u (unipotentGL2 p.2 * p.1))
      (((slabHaar F d₁ d₂).restrict K).prod (pins F Φ).ν) :=
    aestronglyMeasurable_comp_shear_prod F d₁ d₂ Φ hshear _ Measure.restrict_le_self u huK
  have hCc : IsCompact (shear F '' (Kb ×ˢ K')) :=
    (hKb.prod hK').image ((hcont.comp continuous_fst).mul continuous_snd)
  have hφm : AEMeasurable (fun g => ‖u g‖ₑ ^ 2) (slabHaar F d₁ d₂) := huK.enorm.pow_const 2
  have hφinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), ‖u ((γ : AdelicGL2 (𝓞 F) F) * g)‖ₑ ^ 2 = ‖u g‖ₑ ^ 2 :=
    fun γ g => by rw [left_invariant_of_isAutomorphicFnAt F Φ ξ hu γ g]

  have hbound : (∫⁻ g in K, (∫⁻ q, ‖u (unipotentGL2 q * g)‖ₑ ^ 2 ∂(pins F Φ).ν) ∂(slabHaar F d₁ d₂))
      ≤ (m : ENNReal) * ∫⁻ g in Φ, ‖u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂) :=
    (setLIntegral_lintegral_shear_le F d₁ d₂ Φ hslab hshear K K' hK hK' hKK' Kb hKb hbox _ hφm).trans
      (setLIntegral_le_mul_setLIntegral_of_invariant F d₁ d₂ Φ hΦ _ hCc.measurableSet m hm _ hφm hφinv)

  have hu2 : (∫⁻ g in Φ, ‖u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂)) < ⊤ := by
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mp
      (memLp_restrict_Φ_of_isAutomorphicFnAt F Φ ξ hu).2
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h2
    exact lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl) h2
  have hprod : (∫⁻ p, ‖u (unipotentGL2 p.2 * p.1)‖ₑ ^ 2 ∂(((slabHaar F d₁ d₂).restrict K).prod (pins F Φ).ν))
      < ⊤ := by
    rw [lintegral_prod _ (hF.enorm.pow_const 2)]
    exact hbound.trans_lt (ENNReal.mul_lt_top (ENNReal.natCast_lt_top m) hu2)
  have hF2 : MemLp (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => u (unipotentGL2 p.2 * p.1)) 2
      (((slabHaar F d₁ d₂).restrict K).prod (pins F Φ).ν) :=
    ⟨hF, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).mpr
      (by simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using hprod)⟩
  have hF1 := memLp_one_iff_integrable.mp (hF2.mono_exponent (by norm_num))
  have hint : ∀ᵐ g ∂((slabHaar F d₁ d₂).restrict K),
      Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν := by
    filter_upwards [hF1.prod_right_ae] with g hg
    exact hg
  refine ⟨hint, ?_⟩
  refine le_trans ?_ hbound
  refine lintegral_mono_ae ?_
  filter_upwards [hint] with g hg
  exact enorm_integral_sq_le_lintegral_enorm_sq (pins F Φ).ν _ hg.1

private theorem constantTerm_congr_ae
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F)) [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (u v : AdelicGL2 (𝓞 F) F → ℂ) (huv : u =ᵐ[slabHaar F d₁ d₂] v) :
    (fun g => constantTerm (pins F Φ).ν unipotentGL2 u g)
      =ᵐ[slabHaar F d₁ d₂] fun g => constantTerm (pins F Φ).ν unipotentGL2 v g := by
  have _ := hslab
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F
  have hq := quasiMeasurePreserving_shear_prod F d₁ d₂ Φ hshear (slabHaar F d₁ d₂) le_rfl
  have h1 : (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => u (unipotentGL2 p.2 * p.1))
      =ᵐ[(slabHaar F d₁ d₂).prod (pins F Φ).ν]
        (fun p : AdelicGL2 (𝓞 F) F × AdeleRing (𝓞 F) F => v (unipotentGL2 p.2 * p.1)) := hq.ae_eq huv
  have h2 : ∀ᵐ g ∂(slabHaar F d₁ d₂), ∀ᵐ q ∂(pins F Φ).ν, u (unipotentGL2 q * g) = v (unipotentGL2 q * g) :=
    Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with g hg
  simp only [constantTerm, constantTermIntegrand]
  exact integral_congr_ae hg

private theorem constantTerm_add_of_integrable (Φ : Set (AdelicGL2 (𝓞 F) F))
    (u v : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hu : Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν)
    (hv : Integrable (constantTermIntegrand unipotentGL2 v g) (pins F Φ).ν) :
    constantTerm (pins F Φ).ν unipotentGL2 (u + v) g
      = constantTerm (pins F Φ).ν unipotentGL2 u g + constantTerm (pins F Φ).ν unipotentGL2 v g := by
  have h : constantTermIntegrand unipotentGL2 (u + v) g
      = constantTermIntegrand unipotentGL2 u g + constantTermIntegrand unipotentGL2 v g := by
    funext q
    rfl
  simp only [constantTerm, h]
  exact integral_add hu hv

private theorem constantTerm_sub_of_integrable (Φ : Set (AdelicGL2 (𝓞 F) F))
    (u v : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hu : Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν)
    (hv : Integrable (constantTermIntegrand unipotentGL2 v g) (pins F Φ).ν) :
    constantTerm (pins F Φ).ν unipotentGL2 (u - v) g
      = constantTerm (pins F Φ).ν unipotentGL2 u g - constantTerm (pins F Φ).ν unipotentGL2 v g := by
  have h : constantTermIntegrand unipotentGL2 (u - v) g
      = constantTermIntegrand unipotentGL2 u g - constantTermIntegrand unipotentGL2 v g := by
    funext q
    rfl
  simp only [constantTerm, h]
  exact integral_sub hu hv

private theorem constantTerm_linear_combination_of_integrable (Φ : Set (AdelicGL2 (𝓞 F) F))
    (u v : AdelicGL2 (𝓞 F) F → ℂ) (c₁ c₂ : ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hu : Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν)
    (hv : Integrable (constantTermIntegrand unipotentGL2 v g) (pins F Φ).ν) :
    constantTerm (pins F Φ).ν unipotentGL2 (fun x => c₁ * u x + c₂ * v x) g
      = c₁ * constantTerm (pins F Φ).ν unipotentGL2 u g + c₂ * constantTerm (pins F Φ).ν unipotentGL2 v g := by
  have h : constantTermIntegrand unipotentGL2 (fun x => c₁ * u x + c₂ * v x) g
      = fun q => c₁ * constantTermIntegrand unipotentGL2 u g q + c₂ * constantTermIntegrand unipotentGL2 v g q := by
    funext q
    rfl
  simp only [constantTerm, h]
  rw [integral_add (hu.const_mul c₁) (hv.const_mul c₂), integral_const_mul, integral_const_mul]

private theorem ae_integrable_constantTermIntegrand
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q)
    (hdisc : ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C →
      ∃ m : ℕ, ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    ∀ᵐ g ∂(slabHaar F d₁ d₂), Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν := by
  obtain ⟨Kb, hKb, hbox⟩ := exists_isCompact_adelicBox_subset F
  have hpiece : ∀ n : ℕ, ∀ᵐ g ∂(slabHaar F d₁ d₂),
      g ∈ compactCovering (AdelicGL2 (𝓞 F) F) n →
        Integrable (constantTermIntegrand unipotentGL2 u g) (pins F Φ).ν := by
    intro n
    have hKn := isCompact_compactCovering (AdelicGL2 (𝓞 F) F) n
    have hCc : IsCompact (shear F '' (Kb ×ˢ compactCovering (AdelicGL2 (𝓞 F) F) n)) :=
      (hKb.prod hKn).image ((hcont.comp continuous_fst).mul continuous_snd)
    obtain ⟨m, hm⟩ := hdisc _ hCc
    exact ae_imp_of_ae_restrict
      (ae_integrable_and_setLIntegral_constantTerm_sq_le F d₁ d₂ Φ hΦ hslab hshear hcont _ _ hKn.measurableSet hKn
        subset_rfl Kb hKb hbox m hm ξ u hu).1
  have hall := ae_all_iff.mpr hpiece
  filter_upwards [hall] with g hg
  obtain ⟨n, hn⟩ := exists_mem_compactCovering g
  exact hg n hn

private theorem ae_constantTerm_eq_zero_of_tendsto
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q)
    (hdisc : ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C →
      ∃ m : ℕ, ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (ξ : (pins F Φ).Z →* ℂˣ)
    (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (huseq : ∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n))
    (hcusp : ∀ n, ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 (useq n) g = 0)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u)
    (hsub : ∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n - u))
    (hlim : Filter.Tendsto (fun n => eLpNorm (useq n - u) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0)) :
    ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
  obtain ⟨Kb, hKb, hbox⟩ := exists_isCompact_adelicBox_subset F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hiu := ae_integrable_constantTermIntegrand F d₁ d₂ Φ hΦ hslab hshear hcont hdisc ξ u hu
  have hin : ∀ n, ∀ᵐ g ∂(slabHaar F d₁ d₂),
      Integrable (constantTermIntegrand unipotentGL2 (useq n) g) (pins F Φ).ν :=
    fun n => ae_integrable_constantTermIntegrand F d₁ d₂ Φ hΦ hslab hshear hcont hdisc ξ (useq n) (huseq n)

  have hdiff : ∀ n, ∀ᵐ g ∂(slabHaar F d₁ d₂),
      ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2
        = ‖constantTerm (pins F Φ).ν unipotentGL2 (useq n - u) g‖ₑ ^ 2 := by
    intro n
    filter_upwards [hiu, hin n, hcusp n] with g hgu hgn hgc
    rw [constantTerm_sub_of_integrable F Φ (useq n) u g hgn hgu, hgc, zero_sub, enorm_neg]

  have hpiece : ∀ p : ℕ,
      ∫⁻ g in compactCovering (AdelicGL2 (𝓞 F) F) p,
        ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂) = 0 := by
    intro p
    have hKp := isCompact_compactCovering (AdelicGL2 (𝓞 F) F) p
    have hCc : IsCompact (shear F '' (Kb ×ˢ compactCovering (AdelicGL2 (𝓞 F) F) p)) :=
      (hKb.prod hKp).image ((hcont.comp continuous_fst).mul continuous_snd)
    obtain ⟨m, hm⟩ := hdisc _ hCc
    have hle : ∀ n,
        (∫⁻ g in compactCovering (AdelicGL2 (𝓞 F) F) p,
          ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂))
        ≤ (m : ENNReal) * (eLpNorm (useq n - u) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) ^ 2 := by
      intro n
      have h1 : (∫⁻ g in compactCovering (AdelicGL2 (𝓞 F) F) p,
            ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂))
          = ∫⁻ g in compactCovering (AdelicGL2 (𝓞 F) F) p,
            ‖constantTerm (pins F Φ).ν unipotentGL2 (useq n - u) g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂) :=
        lintegral_congr_ae (ae_restrict_of_ae (hdiff n))
      have h2 := (ae_integrable_and_setLIntegral_constantTerm_sq_le F d₁ d₂ Φ hΦ hslab hshear hcont _ _
        hKp.measurableSet hKp subset_rfl Kb hKb hbox m hm ξ _ (hsub n)).2
      have h3 : (∫⁻ g in Φ, ‖(useq n - u) g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂))
          ≤ (eLpNorm (useq n - u) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) ^ 2 := by
        refine (lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl).trans
          (le_of_eq ?_)
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
        simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      calc (∫⁻ g in compactCovering (AdelicGL2 (𝓞 F) F) p,
            ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂))
          = ∫⁻ g in compactCovering (AdelicGL2 (𝓞 F) F) p,
            ‖constantTerm (pins F Φ).ν unipotentGL2 (useq n - u) g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂) := h1
        _ ≤ (m : ENNReal) * ∫⁻ g in Φ, ‖(useq n - u) g‖ₑ ^ 2 ∂(slabHaar F d₁ d₂) := h2
        _ ≤ (m : ENNReal) * (eLpNorm (useq n - u) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) ^ 2 :=
            mul_le_mul_right h3 _
    have h0 : Filter.Tendsto
        (fun n => (eLpNorm (useq n - u) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) ^ 2) Filter.atTop (nhds 0) := by
      have h__af := ((ENNReal.continuous_pow 2).tendsto 0).comp hlim
      simp at h__af
      exact h__af
    have htend : Filter.Tendsto
        (fun n => (m : ENNReal) * (eLpNorm (useq n - u) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) ^ 2)
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.natCast_ne_top m))
    exact nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hle)

  have hae : ∀ p : ℕ, ∀ᵐ g ∂(slabHaar F d₁ d₂),
      g ∈ compactCovering (AdelicGL2 (𝓞 F) F) p → constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
    intro p
    have hmeasp : AEMeasurable (fun g => ‖constantTerm (pins F Φ).ν unipotentGL2 u g‖ₑ ^ 2)
        ((slabHaar F d₁ d₂).restrict (compactCovering (AdelicGL2 (𝓞 F) F) p)) :=
      (aestronglyMeasurable_constantTerm F d₁ d₂ Φ hΦ hshear _ Measure.restrict_le_self ξ u hu).enorm.pow_const 2
    have h0 := (lintegral_eq_zero_iff' hmeasp).mp (hpiece p)
    refine ae_imp_of_ae_restrict ?_
    filter_upwards [h0] with g hg
    simpa using hg
  have hall := ae_all_iff.mpr hae
  filter_upwards [hall] with g hg
  obtain ⟨p, hp⟩ := exists_mem_compactCovering g
  exact hg p hp

private theorem centralScalar_mul_unipotentGL2_comm (z : (AdeleRing (𝓞 F) F)ˣ) (q : AdeleRing (𝓞 F) F) :
    centralScalar (𝓞 F) F z * unipotentGL2 q = unipotentGL2 q * centralScalar (𝓞 F) F z := by
  apply Units.ext
  simp only [Units.val_mul, centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 F) F) (fun _ => Commute.all _ _) _).eq

private theorem constantTerm_centralScalar_mul (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hcentral : ∀ (z : (pins F Φ).Z) (g : AdelicGL2 (𝓞 F) F),
      u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g)
    (z : (pins F Φ).Z) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (pins F Φ).ν unipotentGL2 u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ z : ℂˣ) : ℂ) * constantTerm (pins F Φ).ν unipotentGL2 u g := by
  simp only [constantTerm, constantTermIntegrand]
  rw [← integral_const_mul]
  congr 1
  funext q
  rw [← mul_assoc, ← centralScalar_mul_unipotentGL2_comm, mul_assoc, hcentral]

private theorem aestronglyMeasurable_haar_of_isAutomorphicFnAt
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂)) (hslab : MeasurableSet (slab F d₁ d₂))
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ) (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v) :
    AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨z, hz⟩ := hcover
  have hslabm : AEStronglyMeasurable v (slabHaar F d₁ d₂) :=
    aestronglyMeasurable_slabHaar_of_isAutomorphicFnAt F d₁ d₂ Φ hΦ ξ v hv
  have hkey : ∀ n : ℕ, AEStronglyMeasurable v
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        ((fun g => centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g) ⁻¹' slab F d₁ d₂)) := by
    intro n
    have hmp := (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F)
      (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹)).restrict_preimage hslab
    have hq := hmp.quasiMeasurePreserving
    have h1 : AEStronglyMeasurable (fun g => v (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g))
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          ((fun g => centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g) ⁻¹' slab F d₁ d₂)) :=
      hslabm.comp_quasiMeasurePreserving hq
    refine (h1.const_mul ((ξ (z n) : ℂˣ) : ℂ)).congr (Filter.Eventually.of_forall fun g => ?_)
    have h3 := central_transform_of_isAutomorphicFnAt F Φ ξ hv (z n)
      (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g)
    rw [map_inv, mul_inv_cancel_left] at h3
    exact h3.symm
  have hU : (adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ n : ℕ, (fun g => centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g) ⁻¹' slab F d₁ d₂)
        = adelicGLHaar (Fin 2) (𝓞 F) F := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    filter_upwards [hz] with g hg
    exact Set.mem_iUnion.mpr hg
  rw [← hU]
  exact aestronglyMeasurable_iUnion_iff.mpr hkey

private theorem ae_slabHaar_of_ae_restrict_of_invariant (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂)) (P : AdelicGL2 (𝓞 F) F → Prop)
    (hinv : ∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), P ((γ : AdelicGL2 (𝓞 F) F) * g) ↔ P g)
    (hΦae : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ), P g) :
    ∀ᵐ g ∂(slabHaar F d₁ d₂), P g := by
  have hnull : (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ {g | ¬ P g} = 0 := by
    rw [ae_iff] at hΦae
    exact hΦae
  have hset : ∀ γ : Γ F, γ • {g | ¬ P g} = {g | ¬ P g} := by
    intro γ
    ext g
    have e : P (γ⁻¹ • g) ↔ P g := hinv γ⁻¹ g
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, e]
  have hΦnull : slabHaar F d₁ d₂ ({g | ¬ P g} ∩ Φ) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc slabHaar F d₁ d₂ ({g | ¬ P g} ∩ Φ)
        ≤ adelicGLHaar (Fin 2) (𝓞 F) F ({g | ¬ P g} ∩ Φ) := Measure.le_iff'.mp Measure.restrict_le_self _
      _ ≤ (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ {g | ¬ P g} := Measure.le_restrict_apply _ _
      _ = 0 := hnull
  rw [ae_iff]
  exact hΦ.measure_zero_of_invariant _ hset hΦnull

private theorem ae_haar_of_ae_slabHaar_of_central (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (P : AdelicGL2 (𝓞 F) F → Prop)
    (hP : ∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ (pins F Φ).Z → ∀ g : AdelicGL2 (𝓞 F) F,
      P (centralScalar (𝓞 F) F w * g) → P g)
    (hslabae : ∀ᵐ g ∂(slabHaar F d₁ d₂), P g) : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), P g := by
  obtain ⟨z, hz⟩ := hcover
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have h1 : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), g ∈ slab F d₁ d₂ → P g := ae_imp_of_ae_restrict hslabae
  have h2 : ∀ n : ℕ, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂ →
        P (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g) := by
    intro n
    have hmp := measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F)
      (centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹)
    have hq := hmp.quasiMeasurePreserving
    exact hq.ae (p := fun g => g ∈ slab F d₁ d₂ → P g) h1
  filter_upwards [hz, ae_all_iff.mpr h2] with g hg hg'
  obtain ⟨n, hn⟩ := hg
  exact hP _ ((pins F Φ).Z.inv_mem (z n).2) g (hg' n hn)

private theorem ae_constantTerm_eq_zero_of_ae_restrict_slab
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hcentral : ∀ (z : (pins F Φ).Z) (g : AdelicGL2 (𝓞 F) F),
      u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g)
    (hslabae : ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 u g = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0 := by
  refine ae_haar_of_ae_slabHaar_of_central F d₁ d₂ Φ hcover _ ?_ hslabae
  intro w hw g h
  have h' : constantTerm (pins F Φ).ν unipotentGL2 u (centralScalar (𝓞 F) F w * g)
      = ((ξ ⟨w, hw⟩ : ℂˣ) : ℂ) * constantTerm (pins F Φ).ν unipotentGL2 u g :=
    constantTerm_centralScalar_mul F Φ ξ u hcentral ⟨w, hw⟩ g
  rw [h'] at h
  exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero _)

private theorem ae_constantTerm_eq_zero_iff_ae_restrict_slab
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0) ↔
      (∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 u g = 0)) := by
  refine ⟨fun h => ae_restrict_of_ae h, fun h => ?_⟩
  exact ae_constantTerm_eq_zero_of_ae_restrict_slab F d₁ d₂ Φ hcover ξ u
    (central_transform_of_isAutomorphicFnAt F Φ ξ hu) h

private theorem ae_constantTerm_eq_zero_of_tendsto_haar
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q)
    (hdisc : ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C →
      ∃ m : ℕ, ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ)
    (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (huseq : ∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n))
    (hcusp : ∀ n, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 (useq n) g = 0)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hsub : ∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n - v))
    (hlim : Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0)) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v g = 0 := by
  have hcusp' : ∀ n, ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 (useq n) g = 0 :=
    fun n => ae_restrict_of_ae (hcusp n)
  exact ae_constantTerm_eq_zero_of_ae_restrict_slab F d₁ d₂ Φ hcover ξ v
    (central_transform_of_isAutomorphicFnAt F Φ ξ hv)
    (ae_constantTerm_eq_zero_of_tendsto F d₁ d₂ Φ hΦ hslab hshear hcont hdisc ξ useq huseq hcusp' v hv hsub hlim)

private theorem ae_constantTerm_eq_zero_of_ae_eq_restrict
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q)
    (hdisc : ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C →
      ∃ m : ℕ, ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ)
    (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ) (h₁ : IsAutomorphicFnAt F (pins F Φ) ξ v₁)
    (h₂ : IsAutomorphicFnAt F (pins F Φ) ξ v₂) (h₁₂ : v₁ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v₂)
    (hc₁ : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0 := by
  have _ := hcont
  have _ := hdisc

  have hslabeq : v₁ =ᵐ[slabHaar F d₁ d₂] v₂ := by
    have hnull : (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ {g | v₁ g ≠ v₂ g} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at h₁₂
      simpa using h₁₂
    have hinv : ∀ γ : Γ F, γ • {g | v₁ g ≠ v₂ g} = {g | v₁ g ≠ v₂ g} := by
      intro γ
      ext g
      have e₁ : v₁ (γ⁻¹ • g) = v₁ g := left_invariant_of_isAutomorphicFnAt F Φ ξ h₁ γ⁻¹ g
      have e₂ : v₂ (γ⁻¹ • g) = v₂ g := left_invariant_of_isAutomorphicFnAt F Φ ξ h₂ γ⁻¹ g
      simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, e₁, e₂]
    have hΦnull : slabHaar F d₁ d₂ ({g | v₁ g ≠ v₂ g} ∩ Φ) = 0 := by
      refine nonpos_iff_eq_zero.mp ?_
      calc slabHaar F d₁ d₂ ({g | v₁ g ≠ v₂ g} ∩ Φ)
          ≤ adelicGLHaar (Fin 2) (𝓞 F) F ({g | v₁ g ≠ v₂ g} ∩ Φ) := Measure.restrict_le_self _
        _ ≤ (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ {g | v₁ g ≠ v₂ g} := Measure.le_restrict_apply _ _
        _ = 0 := hnull
    have := hΦ.measure_zero_of_invariant _ hinv hΦnull
    rw [Filter.EventuallyEq, ae_iff]
    simpa using this
  have hCT := constantTerm_congr_ae F d₁ d₂ Φ hslab hshear v₁ v₂ hslabeq
  have hc₁' : ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0 := ae_restrict_of_ae hc₁
  have hc₂' : ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0 := by
    filter_upwards [hCT, hc₁'] with g hg hg₁
    rw [← hg]
    exact hg₁
  exact ae_constantTerm_eq_zero_of_ae_restrict_slab F d₁ d₂ Φ hcover ξ v₂
    (central_transform_of_isAutomorphicFnAt F Φ ξ h₂) hc₂'

private theorem ae_constantTerm_linear_combination_eq_zero
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F d₁ d₂)]
    [SigmaCompactSpace (AdelicGL2 (𝓞 F) F)]
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hslab : MeasurableSet (slab F d₁ d₂)) (hshear : Measurable (shear F))
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q)
    (hdisc : ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C →
      ∃ m : ℕ, ∀ g : AdelicGL2 (𝓞 F) F, {γ : Γ F | (γ : AdelicGL2 (𝓞 F) F) * g ∈ C}.encard ≤ m)
    (hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
        centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂)
    (ξ : (pins F Φ).Z →* ℂˣ)
    (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ) (c₁ c₂ : ℂ) (h₁ : IsAutomorphicFnAt F (pins F Φ) ξ v₁)
    (h₂ : IsAutomorphicFnAt F (pins F Φ) ξ v₂)
    (hc₁ : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0)
    (hc₂ : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      constantTerm (pins F Φ).ν unipotentGL2 (fun g => c₁ * v₁ g + c₂ * v₂ g) g = 0 := by
  have hi₁ := ae_integrable_constantTermIntegrand F d₁ d₂ Φ hΦ hslab hshear hcont hdisc ξ v₁ h₁
  have hi₂ := ae_integrable_constantTermIntegrand F d₁ d₂ Φ hΦ hslab hshear hcont hdisc ξ v₂ h₂
  have hc₁' : ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0 := ae_restrict_of_ae hc₁
  have hc₂' : ∀ᵐ g ∂(slabHaar F d₁ d₂), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0 := ae_restrict_of_ae hc₂
  have hslabae : ∀ᵐ g ∂(slabHaar F d₁ d₂),
      constantTerm (pins F Φ).ν unipotentGL2 (fun g => c₁ * v₁ g + c₂ * v₂ g) g = 0 := by
    filter_upwards [hi₁, hi₂, hc₁', hc₂'] with g hg₁ hg₂ hz₁ hz₂
    rw [constantTerm_linear_combination_of_integrable F Φ v₁ v₂ c₁ c₂ g hg₁ hg₂, hz₁, hz₂, mul_zero, mul_zero,
      add_zero]
  refine ae_constantTerm_eq_zero_of_ae_restrict_slab F d₁ d₂ Φ hcover ξ _ ?_ hslabae
  intro z g
  simp only [central_transform_of_isAutomorphicFnAt F Φ ξ h₁ z g, central_transform_of_isAutomorphicFnAt F Φ ξ h₂ z g]
  ring

end AutomorphicForm.LsXiOrthogonalSplit

end

end

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab.AutomorphicForm"
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
namespace LsXiOrthogonalSplit
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem ideleNorm_one_eq : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
  rw [one_mul] at h
  have h' : NumberField.TateGlobal.ideleNorm F 1 * 1
      = NumberField.TateGlobal.ideleNorm F 1 * NumberField.TateGlobal.ideleNorm F 1 := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := F) 1).ne' h').symm

private theorem ideleNorm_inv_eq (w : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F w⁻¹ = (NumberField.TateGlobal.ideleNorm F w)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := F) w w⁻¹
  rw [mul_inv_cancel, ideleNorm_one_eq] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem det_centralScalar_eq (w : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F w) = w ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem ideleNorm_det_centralScalar_inv_mul (w : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F w⁻¹ * g))
      = (NumberField.TateGlobal.ideleNorm F w)⁻¹ * (NumberField.TateGlobal.ideleNorm F w)⁻¹
          * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar_eq, sq, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_inv_eq]

private theorem globalPoints_mul_mem_slab_iff (a b : ℝ)
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (γ : Γ F) (g : AdelicGL2 (𝓞 F) F) : (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b ↔ g ∈ slab F a b := by
  obtain ⟨x, hx⟩ := γ.2
  have hdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ← hx, hpf x, one_mul]
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g)) ∈ Set.Icc a b ↔
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b
  rw [hdet]

private theorem smulInvariantMeasure_slabHaar (a b : ℝ) (hslab : MeasurableSet (slab F a b))
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1) :
    SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b) := by
  have _ := hslab
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hpre : (fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' slab F a b = slab F a b := by
    ext g
    exact globalPoints_mul_mem_slab_iff F a b hpf γ g
  have hmeas : MeasurableSet ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s) :=
    measurable_const_mul (γ : AdelicGL2 (𝓞 F) F) hs
  calc slabHaar F a b ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s)
      = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s ∩ slab F a b) :=
        Measure.restrict_apply hmeas
    _ = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' (s ∩ slab F a b)) := by
        rw [Set.preimage_inter, hpre]
    _ = adelicGLHaar (Fin 2) (𝓞 F) F (s ∩ slab F a b) :=
        measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) _
    _ = slabHaar F a b s := (Measure.restrict_apply hs).symm

private theorem exists_central_cover_slab (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hnorm : ∀ t : ℝ, 0 < t → ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = t) :
    ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
      centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂ := by
  have hρ0 : 0 < d₂ / d₁ := div_pos (hd₁.trans hd) hd₁
  have hρ1 : 1 < d₂ / d₁ := (one_lt_div hd₁).mpr hd
  have hρd : d₂ / d₁ * d₁ = d₂ := div_mul_cancel₀ d₂ hd₁.ne'
  choose zk hzk using fun k : ℤ => hnorm (Real.sqrt ((d₂ / d₁) ^ k)) (Real.sqrt_pos.mpr (zpow_pos hρ0 k))
  have hmem : ∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ (pins F Φ).Z := fun w => Subgroup.mem_top w
  refine ⟨fun n => ⟨zk ((Denumerable.eqv ℤ).symm n), hmem _⟩, Filter.Eventually.of_forall fun g => ?_⟩
  have ht : 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.ideleNorm_pos (F := F) _
  obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (div_pos ht hd₁) hρ1
  refine ⟨Denumerable.eqv ℤ k, ?_⟩
  simp only [Equiv.symm_apply_apply]
  have hρk : 0 < (d₂ / d₁) ^ k := zpow_pos hρ0 k
  have hval : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (zk k)⁻¹ * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) / (d₂ / d₁) ^ k := by
    rw [ideleNorm_det_centralScalar_inv_mul, hzk, ← mul_inv, Real.mul_self_sqrt hρk.le, inv_mul_eq_div]
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (zk k)⁻¹ * g))
    ∈ Set.Icc d₁ d₂
  rw [hval]
  have h1 : (d₂ / d₁) ^ k * d₁ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    (le_div_iff₀ hd₁).mp hk.1
  have h2 : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) < (d₂ / d₁) ^ (k + 1) * d₁ :=
    (div_lt_iff₀ hd₁).mp hk.2
  rw [zpow_add_one₀ hρ0.ne', mul_assoc, hρd] at h2
  constructor
  · rw [le_div_iff₀ hρk]
    linarith
  · rw [div_le_iff₀ hρk]
    linarith

end AutomorphicForm.LsXiOrthogonalSplit

end

section

set_option autoImplicit false

open NumberField
open scoped NumberField Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem chiDet_mul_right (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g y : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F χ (g * y)
      = chiDet (𝓞 F) F χ g * ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  simp only [chiDet, map_mul, Units.val_mul]

private theorem exists_det_eq (t : (AdeleRing (𝓞 F) F)ˣ) :
    ∃ y : AdelicGL2 (𝓞 F) F, Matrix.GeneralLinearGroup.det y = t := by
  have hdet : Matrix.det (Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1])
      = (t : AdeleRing (𝓞 F) F) := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hdet]; exact t.isUnit), ?_⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hdet

private theorem exists_apply_det_ne {χ χ' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hne : χ ≠ χ') :
    ∃ y : AdelicGL2 (𝓞 F) F,
      χ (Matrix.GeneralLinearGroup.det y) ≠ χ' (Matrix.GeneralLinearGroup.det y) := by
  obtain ⟨t, ht⟩ : ∃ t : (AdeleRing (𝓞 F) F)ˣ, χ t ≠ χ' t := by
    by_contra hall
    exact hne (MonoidHom.ext fun t => by
      by_contra h
      exact hall ⟨t, h⟩)
  obtain ⟨y, hy⟩ := exists_det_eq F t
  exact ⟨y, by rw [hy]; exact ht⟩

private theorem isAutomorphicFnAt_chiDet_of_isAutomorphicFnAt_sum (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ)
    (hadd : ∀ v w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ v →
      IsAutomorphicFnAt F pins ξ w → IsAutomorphicFnAt F pins ξ (v + w))
    (hsmul : ∀ (v : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ), IsAutomorphicFnAt F pins ξ v →
      IsAutomorphicFnAt F pins ξ (c • v))
    (htrans : ∀ w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ w →
      ∀ y : AdelicGL2 (𝓞 F) F, IsAutomorphicFnAt F pins ξ (fun g => w (g * y)))
    (χ₀ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (t : Finset ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) :
    ∀ a : ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) → ℂ, χ₀ ∈ t → a χ₀ ≠ 0 →
      IsAutomorphicFnAt F pins ξ (∑ χ ∈ t, a χ • chiDet (𝓞 F) F χ) →
      IsAutomorphicFnAt F pins ξ (chiDet (𝓞 F) F χ₀) := by
  induction t using Finset.strongInduction with
  | H t ih =>
    intro a hχ₀ ha hsum
    by_cases hall : ∀ χ ∈ t, χ = χ₀
    · have ht : t = {χ₀} := by
        ext χ
        rw [Finset.mem_singleton]
        exact ⟨fun hχ => hall χ hχ, fun hχ => hχ ▸ hχ₀⟩
      rw [ht, Finset.sum_singleton] at hsum
      have := hsmul _ (a χ₀)⁻¹ hsum
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    · obtain ⟨χ₁, hχ₁, hne⟩ : ∃ χ₁ ∈ t, χ₁ ≠ χ₀ := by
        by_contra hcon
        exact hall fun χ hχ => by
          by_contra h
          exact hcon ⟨χ, hχ, h⟩
      obtain ⟨y, hy⟩ := exists_apply_det_ne F hne.symm
      have herase : ∑ χ ∈ t.erase χ₁,
            (a χ * (((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)
              - ((χ₁ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) • chiDet (𝓞 F) F χ
          = ∑ χ ∈ t,
            (a χ * (((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)
              - ((χ₁ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) • chiDet (𝓞 F) F χ :=
        Finset.sum_erase t (by simp)
      have hkey : (fun g => (∑ χ ∈ t, a χ • chiDet (𝓞 F) F χ) (g * y))
            + (-((χ₁ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) • ∑ χ ∈ t, a χ • chiDet (𝓞 F) F χ
          = ∑ χ ∈ t.erase χ₁,
            (a χ * (((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)
              - ((χ₁ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) • chiDet (𝓞 F) F χ := by
        rw [herase]
        funext g
        simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, chiDet_mul_right, smul_eq_mul,
          Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun χ _ => ?_
        ring
      have hauto : IsAutomorphicFnAt F pins ξ (∑ χ ∈ t.erase χ₁,
          (a χ * (((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)
            - ((χ₁ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ))) • chiDet (𝓞 F) F χ) := by
        rw [← hkey]
        exact hadd _ _ (htrans _ hsum y) (hsmul _ _ hsum)
      refine ih (t.erase χ₁) (Finset.erase_ssubset hχ₁) _ (Finset.mem_erase.2 ⟨hne.symm, hχ₀⟩)
        (mul_ne_zero ha (sub_ne_zero.2 fun h => hy (Units.ext h))) hauto

private theorem exists_automorphic_generators_of_mem_residualSpan (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ)
    (hadd : ∀ v w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ v →
      IsAutomorphicFnAt F pins ξ w → IsAutomorphicFnAt F pins ξ (v + w))
    (hsmul : ∀ (v : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ), IsAutomorphicFnAt F pins ξ v →
      IsAutomorphicFnAt F pins ξ (c • v))
    (htrans : ∀ w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ w →
      ∀ y : AdelicGL2 (𝓞 F) F, IsAutomorphicFnAt F pins ξ (fun g => w (g * y)))
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsAutomorphicFnAt F pins ξ h)
    (hmem : h ∈ residualSpan (𝓞 F) F pins.Z ξ) :
    ∃ (s : Finset ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (c : ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) → ℂ),
      (∀ χ ∈ s, SquaresToXi (𝓞 F) F pins.Z ξ χ)
      ∧ (∀ χ ∈ s, IsAutomorphicFnAt F pins ξ (chiDet (𝓞 F) F χ))
      ∧ h = ∑ χ ∈ s, c χ • chiDet (𝓞 F) F χ := by
  have himg : ({φ | ∃ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
        SquaresToXi (𝓞 F) F pins.Z ξ χ ∧ φ = chiDet (𝓞 F) F χ} : Set (AdelicGL2 (𝓞 F) F → ℂ))
      = chiDet (𝓞 F) F '' {χ | SquaresToXi (𝓞 F) F pins.Z ξ χ} := by
    ext φ
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      exact ⟨χ, hχ, rfl⟩
    · rintro ⟨χ, hχ, rfl⟩
      exact ⟨χ, hχ, rfl⟩
  have hmem' : h ∈ Submodule.span ℂ (chiDet (𝓞 F) F '' {χ | SquaresToXi (𝓞 F) F pins.Z ξ χ}) := by
    rw [← himg]
    exact hmem
  rw [Finsupp.mem_span_image_iff_linearCombination] at hmem'
  obtain ⟨l, hl, hlh⟩ := hmem'
  rw [Finsupp.mem_supported] at hl
  simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hlh
  refine ⟨l.support, l, fun χ hχ => hl hχ, fun χ₀ hχ₀ => ?_, hlh.symm⟩
  refine isAutomorphicFnAt_chiDet_of_isAutomorphicFnAt_sum F pins ξ hadd hsmul htrans χ₀ l.support
    l hχ₀ (Finsupp.mem_support_iff.1 hχ₀) ?_
  rw [hlh]
  exact hh

end AutomorphicForm

end

end

section

set_option autoImplicit false

p2m_open "MeasureTheory Measure MeasureTheory.Measure Filter"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

private theorem exists_ae_eq_const_of_forall_ae_comp_mul_right (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsMulRightInvariant] [SFinite μ] {ψ : G → ℂ} (hψm : AEStronglyMeasurable ψ μ)
    (hψ : ∀ y : G, ∀ᵐ g ∂μ, ψ (g * y) = ψ g) :
    ∃ c : ℂ, ψ =ᵐ[μ] fun _ => c := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · exact ⟨0, by simp [Filter.EventuallyEq]⟩
  obtain ⟨ψ', hψ'm, hψψ'⟩ : ∃ ψ' : G → ℂ, Measurable ψ' ∧ ψ =ᵐ[μ] ψ' :=
    ⟨hψm.mk ψ, hψm.stronglyMeasurable_mk.measurable, hψm.ae_eq_mk⟩
  have hψ' : ∀ y : G, ∀ᵐ g ∂μ, ψ' (g * y) = ψ' g := by
    intro y
    have h1 : ∀ᵐ g ∂μ, ψ (g * y) = ψ' (g * y) :=
      (measurePreserving_mul_right μ y).quasiMeasurePreserving.ae hψψ'
    filter_upwards [h1, hψ y, hψψ'] with g h1 h2 h3
    rw [← h1, h2, h3]
  have hmeas : MeasurableSet {x : G × G | ψ' (x.1 * x.2) = ψ' x.1} :=
    measurableSet_eq_fun (hψ'm.comp measurable_mul) (hψ'm.comp measurable_fst)
  have hcomm : ∀ᵐ g ∂μ, ∀ᵐ y ∂μ, ψ' (g * y) = ψ' g :=
    (ae_ae_comm hmeas).2 (Eventually.of_forall hψ')
  haveI : (ae μ).NeBot := ae_neBot.2 hμ
  obtain ⟨g₀, hg₀⟩ := hcomm.exists
  refine ⟨ψ' g₀, ?_⟩
  have hset : MeasurableSet {h : G | ψ' h = ψ' g₀} := measurableSet_eq_fun hψ'm measurable_const
  have hall : ∀ᵐ h ∂μ, ψ' h = ψ' g₀ := by
    rw [← (measurePreserving_mul_left μ g₀).map_eq]
    exact (ae_map_iff (measurable_const_mul g₀).aemeasurable hset).2 hg₀
  exact hψψ'.trans (hall : ψ' =ᵐ[μ] fun _ => ψ' g₀)

end AutomorphicForm

end

section

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem setIntegral_mul_conj_eq_zero_of_mem_residualSpan (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (μ : Measure (AdelicGL2 (𝓞 F) F)) (D : Set (AdelicGL2 (𝓞 F) F))
    (hmemLp : ∀ w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ w → MemLp w 2 (μ.restrict D))
    (hadd : ∀ v w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ v →
      IsAutomorphicFnAt F pins ξ w → IsAutomorphicFnAt F pins ξ (v + w))
    (hsmul : ∀ (v : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ), IsAutomorphicFnAt F pins ξ v →
      IsAutomorphicFnAt F pins ξ (c • v))
    (htrans : ∀ w : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F pins ξ w →
      ∀ y : AdelicGL2 (𝓞 F) F, IsAutomorphicFnAt F pins ξ (fun g => w (g * y)))
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F pins ξ v)
    (hgen : ∀ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsAutomorphicFnAt F pins ξ (chiDet (𝓞 F) F χ) →
      ∫ g in D, v g * (starRingEnd ℂ) (chiDet (𝓞 F) F χ g) ∂μ = 0) :
    ∀ (h : AdelicGL2 (𝓞 F) F → ℂ), IsAutomorphicFnAt F pins ξ h →
      h ∈ residualSpan (𝓞 F) F pins.Z ξ →
      ∫ g in D, v g * (starRingEnd ℂ) (h g) ∂μ = 0 := by
  intro h hh hmem
  obtain ⟨s, c, -, hauto, hsum⟩ :=
    exists_automorphic_generators_of_mem_residualSpan F pins ξ hadd hsmul htrans h hh hmem
  rw [hsum]
  have hpt : ∀ g : AdelicGL2 (𝓞 F) F,
      v g * (starRingEnd ℂ) ((∑ χ ∈ s, c χ • chiDet (𝓞 F) F χ) g)
        = ∑ χ ∈ s, (starRingEnd ℂ) (c χ) * (v g * (starRingEnd ℂ) (chiDet (𝓞 F) F χ g)) := by
    intro g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ _ => by ring
  simp only [hpt]
  have hint : ∀ χ ∈ s, Integrable
      (fun g => (starRingEnd ℂ) (c χ) * (v g * (starRingEnd ℂ) (chiDet (𝓞 F) F χ g)))
      (μ.restrict D) := by
    intro χ hχ
    have hprod : Integrable (v * star (chiDet (𝓞 F) F χ)) (μ.restrict D) :=
      (hmemLp v hv).integrable_mul (hmemLp _ (hauto χ hχ)).star
    exact (hprod.const_mul ((starRingEnd ℂ) (c χ))).congr
      (Filter.Eventually.of_forall fun g => by simp only [Pi.mul_apply, Pi.star_apply,
        starRingEnd_apply])
  rw [integral_finsetSum s hint]
  exact Finset.sum_eq_zero fun χ hχ => by rw [integral_const_mul, hgen χ (hauto χ hχ), mul_zero]

private theorem measurable_unipotentGL2_fst_mul_snd [SecondCountableTopology (AdelicGL2 (𝓞 F) F)]
    (hcont : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q) :
    Measurable fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => unipotentGL2 p.1 * p.2 :=
  ((hcont.comp continuous_fst).mul continuous_snd).measurable

end AutomorphicForm

end

end

section

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab.AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt isAutomorphicFnAt_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar SquaresToXi IsLsXiFunction chiDet unipotentGL2 unipotentGL2_coe constantTermIntegrand constantTerm residualSpan ideleNorm_det_globalPoints"
namespace LsXiOrthogonalSplit
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (X : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * X = X * centralScalar (𝓞 F) F z := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    = (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

private theorem det_centralScalar_eq_sq (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem mem_slab_iff (d₁ d₂ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    g ∈ slab F d₁ d₂ ↔ d₁ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∧
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ d₂ :=
  Set.mem_Icc

private theorem preimage_mul_right_slab (d₁ d₂ : ℝ) (y : AdelicGL2 (𝓞 F) F) :
    (fun g : AdelicGL2 (𝓞 F) F => g * y) ⁻¹' slab F d₁ d₂ =
      slab F (d₁ * (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))⁻¹)
        (d₂ * (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))⁻¹) := by
  set t := NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) with ht_def
  have ht : 0 < t := NumberField.TateGlobal.ideleNorm_pos _
  ext g
  have hmul : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (g * y)) =
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) * t := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  simp only [Set.mem_preimage, mem_slab_iff, hmul]
  rw [← le_div_iff₀ ht, ← div_le_iff₀ ht, div_eq_mul_inv, div_eq_mul_inv]

private theorem image_mul_right_subset_slab (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ slab F d₁ d₂)
    (y : AdelicGL2 (𝓞 F) F) :
    (· * y) '' Φ ⊆ slab F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
      (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)) := by
  have ht : 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.ideleNorm_pos _
  rintro _ ⟨g, hg, rfl⟩
  have h := (mem_slab_iff F d₁ d₂ g).1 (hΦs hg)
  rw [mem_slab_iff, map_mul, NumberField.TateGlobal.ideleNorm_mul]
  exact ⟨mul_le_mul_of_nonneg_right h.1 ht.le, mul_le_mul_of_nonneg_right h.2 ht.le⟩

private theorem isLsXiFunction_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).1 hu).1

private theorem memLp_of_isAutomorphicFnAt (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
  ((lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).1 hu).2

private theorem isAutomorphicFnAt_of_isLsXiFunction_of_memLp (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (pins F Φ).Z →* ℂˣ) (u : AdelicGL2 (𝓞 F) F → ℂ) (h1 : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u)
    (h2 : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) : IsAutomorphicFnAt F (pins F Φ) ξ u :=
  (lsXiMemberAt_iff (𝓞 F) F (pins F Φ).μ (pins F Φ).Z ξ (pins F Φ).D u).2 ⟨h1, h2⟩

private theorem smul_invariant_mul_conj (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u w : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u)
    (hw : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ w) (y : AdelicGL2 (𝓞 F) F) :
    ∀ (γ : Γ F) (x : AdelicGL2 (𝓞 F) F),
      (fun g => u g * (starRingEnd ℂ) (w (g * y))) (γ • x) = (fun g => u g * (starRingEnd ℂ) (w (g * y))) x := by
  intro γ x
  obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.1 γ.2
  show u ((γ : AdelicGL2 (𝓞 F) F) * x) * (starRingEnd ℂ) (w ((γ : AdelicGL2 (𝓞 F) F) * x * y)) =
    u x * (starRingEnd ℂ) (w (x * y))
  rw [← hγ₀, mul_assoc, hu.left_invariant, hw.left_invariant]

private theorem smul_invariant_enorm_sq (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsLsXiFunction (𝓞 F) F (pins F Φ).Z ξ u) :
    ∀ (γ : Γ F) (x : AdelicGL2 (𝓞 F) F), (fun g => ‖u g‖ₑ ^ 2) (γ • x) = (fun g => ‖u g‖ₑ ^ 2) x := by
  intro γ x
  obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.1 γ.2
  show ‖u ((γ : AdelicGL2 (𝓞 F) F) * x)‖ₑ ^ 2 = ‖u x‖ₑ ^ 2
  rw [← hγ₀, hu.left_invariant]

private theorem image_centralScalar_mul_subset_slab (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hΦs : Φ ⊆ slab F d₁ d₂) (z : (AdeleRing (𝓞 F) F)ˣ) :
    (centralScalar (𝓞 F) F z * ·) '' Φ ⊆ slab F (d₁ * NumberField.TateGlobal.ideleNorm F z ^ 2)
      (d₂ * NumberField.TateGlobal.ideleNorm F z ^ 2) := by
  have hset : ((centralScalar (𝓞 F) F z * ·) '' Φ) = ((· * centralScalar (𝓞 F) F z) '' Φ) :=
    Set.image_congr fun g _ => centralScalar_mul_comm F z g
  have hnorm : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z))
      = NumberField.TateGlobal.ideleNorm F z ^ 2 := by
    rw [det_centralScalar_eq_sq, pow_two, pow_two, NumberField.TateGlobal.ideleNorm_mul]
  rw [hset, ← hnorm]
  exact image_mul_right_subset_slab F d₁ d₂ Φ hΦs _

private theorem ideleNorm_one' : NumberField.TateGlobal.ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 F) F)ˣ) 1
  rw [one_mul] at h
  exact (mul_eq_left₀ (NumberField.TateGlobal.ideleNorm_pos _).ne').1 h.symm

private theorem ideleNorm_inv' (x : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.TateGlobal.ideleNorm F x⁻¹ = (NumberField.TateGlobal.ideleNorm F x)⁻¹ := by
  have h : NumberField.TateGlobal.ideleNorm F x⁻¹ * NumberField.TateGlobal.ideleNorm F x = 1 := by
    rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one']
  exact eq_inv_of_mul_eq_one_left h

private theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

private theorem chiDet_mul (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g y : AdelicGL2 (𝓞 F) F) :
    chiDet (𝓞 F) F χ (g * y) = chiDet (𝓞 F) F χ g * chiDet (𝓞 F) F χ y := by
  simp only [chiDet, map_mul, Units.val_mul]

private theorem chiDet_unipotentGL2_mul (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) : chiDet (𝓞 F) F χ (unipotentGL2 x * g) = chiDet (𝓞 F) F χ g := by
  rw [chiDet_mul, chiDet, det_unipotentGL2, map_one, Units.val_one, one_mul]

private theorem chiDet_ne_zero (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (g : AdelicGL2 (𝓞 F) F) : chiDet (𝓞 F) F χ g ≠ 0 :=
  Units.ne_zero _

private theorem isFundamentalDomain_image_mul_right
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    (hslab : ∀ a b : ℝ, MeasurableSet (slab F a b))
    (hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant)
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂)) (y : AdelicGL2 (𝓞 F) F) :
    IsFundamentalDomain (Γ F) ((· * y) '' Φ)
      (slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
        (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))) := by
  haveI := hright

  have hpre : (fun g : AdelicGL2 (𝓞 F) F => g * y⁻¹) ⁻¹' slab F d₁ d₂ =
      slab F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
        (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)) := by
    rw [preimage_mul_right_slab, map_inv, ideleNorm_inv', inv_inv]
  have h0 : MeasurePreserving (fun g : AdelicGL2 (𝓞 F) F => g * y⁻¹)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict ((fun g : AdelicGL2 (𝓞 F) F => g * y⁻¹) ⁻¹' slab F d₁ d₂))
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) :=
    (measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) y⁻¹).restrict_preimage (hslab d₁ d₂)
  rw [hpre] at h0
  have hqmp : Measure.QuasiMeasurePreserving (⇑(Equiv.mulRight y).symm)
      (slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
        (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)))
      (slabHaar F d₁ d₂) :=
    h0.quasiMeasurePreserving
  have hsemi : ∀ γ : Γ F, Function.Semiconj (⇑(Equiv.mulRight y))
      (fun x => (Equiv.refl (Γ F)) γ • x) (fun x => γ • x) := by
    intro γ x
    simp only [Equiv.coe_mulRight, Equiv.refl_apply, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact hΦ.image_of_equiv (Equiv.mulRight y) hqmp (Equiv.refl _) hsemi

private theorem isFundamentalDomain_image_centralScalar_mul
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F))
    [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    (hslab : ∀ a b : ℝ, MeasurableSet (slab F a b))
    (hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant)
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂)) (z : (AdeleRing (𝓞 F) F)ˣ) :
    IsFundamentalDomain (Γ F) ((centralScalar (𝓞 F) F z * ·) '' Φ)
      (slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F z ^ 2)
        (d₂ * NumberField.TateGlobal.ideleNorm F z ^ 2)) := by

  have hset : ((centralScalar (𝓞 F) F z * ·) '' Φ) = ((· * centralScalar (𝓞 F) F z) '' Φ) := by
    refine Set.image_congr fun g _ => ?_
    exact centralScalar_mul_comm F z g
  have hnorm : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z))
      = NumberField.TateGlobal.ideleNorm F z ^ 2 := by
    rw [det_centralScalar_eq_sq, pow_two, pow_two, NumberField.TateGlobal.ideleNorm_mul]
  rw [hset, ← hnorm]
  exact isFundamentalDomain_image_mul_right F d₁ d₂ Φ hslab hright hΦ (centralScalar (𝓞 F) F z)

private theorem setIntegral_comp_mul_right_mul_conj_eq
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ slab F d₁ d₂)
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    (hslab : ∀ a b : ℝ, MeasurableSet (slab F a b))
    (hinv : ∀ a b : ℝ, SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b))
    (hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant)
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (ξ : (pins F Φ).Z →* ℂˣ) (u w : AdelicGL2 (𝓞 F) F → ℂ)
    (hu : IsAutomorphicFnAt F (pins F Φ) ξ u) (hw : IsAutomorphicFnAt F (pins F Φ) ξ w)
    (y : AdelicGL2 (𝓞 F) F) (z : (pins F Φ).Z)
    (hz : NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ 2 =
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)) :
    ∫ g in Φ, u (g * y) * (starRingEnd ℂ) (w g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2 : ℝ) *
        ∫ g in Φ, u g * (starRingEnd ℂ) (w (g * y⁻¹)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := hright
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have huL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ u hu
  have hwL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ w hw
  have ht : 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.ideleNorm_pos _

  have hFD1 := isFundamentalDomain_image_mul_right F d₁ d₂ Φ hslab hright hΦ y
  have hFD2 := isFundamentalDomain_image_centralScalar_mul F d₁ d₂ Φ hslab hright hΦ
    (z : (AdeleRing (𝓞 F) F)ˣ)
  rw [hz] at hFD2
  have hA1 := image_mul_right_subset_slab F d₁ d₂ Φ hΦs y
  have hA2 := image_centralScalar_mul_subset_slab F d₁ d₂ Φ hΦs (z : (AdeleRing (𝓞 F) F)ˣ)
  rw [hz] at hA2
  haveI := hinv (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
    (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))

  have hGinv := smul_invariant_mul_conj F Φ ξ u w huL hwL y⁻¹
  have hEmbR : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 F) F => g * y) :=
    (MeasurableEquiv.mulRight y).measurableEmbedding
  have hEmbL : MeasurableEmbedding
      (fun g : AdelicGL2 (𝓞 F) F => centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) :=
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ))).measurableEmbedding
  have hξ : ((ξ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ξ z : ℂˣ) : ℂ) =
      (((‖((ξ z : ℂˣ) : ℂ)‖ ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  calc ∫ g in Φ, u (g * y) * (starRingEnd ℂ) (w g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ g in (· * y) '' Φ, u g * (starRingEnd ℂ) (w (g * y⁻¹)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [(measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) y).setIntegral_image_emb hEmbR]
        simp only [mul_inv_cancel_right]
    _ = ∫ g in (· * y) '' Φ, u g * (starRingEnd ℂ) (w (g * y⁻¹))
          ∂(slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
            (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))) := by
        simp only [slabHaar, Measure.restrict_restrict_of_subset hA1]
    _ = ∫ g in (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * ·) '' Φ,
          u g * (starRingEnd ℂ) (w (g * y⁻¹))
          ∂(slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
            (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))) :=
        hFD1.setIntegral_eq hFD2 hGinv
    _ = ∫ g in (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * ·) '' Φ,
          u g * (starRingEnd ℂ) (w (g * y⁻¹)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        simp only [slabHaar, Measure.restrict_restrict_of_subset hA2]
    _ = ∫ g in Φ, u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) *
          (starRingEnd ℂ) (w (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g * y⁻¹))
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        (measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F) _).setIntegral_image_emb hEmbL _ Φ
    _ = ∫ g in Φ, (((‖((ξ z : ℂˣ) : ℂ)‖ ^ 2 : ℝ)) : ℂ) * (u g * (starRingEnd ℂ) (w (g * y⁻¹)))
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        congr 1
        funext g
        rw [mul_assoc, huL.central_transform z g, hwL.central_transform z (g * y⁻¹), map_mul, ← hξ]
        ring
    _ = (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2 : ℝ) *
          ∫ g in Φ, u g * (starRingEnd ℂ) (w (g * y⁻¹)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [integral_const_mul]

private theorem isAutomorphicFnAt_comp_mul_right
    (d₁ d₂ : ℝ) (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ slab F d₁ d₂)
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    (hslab : ∀ a b : ℝ, MeasurableSet (slab F a b))
    (hinv : ∀ a b : ℝ, SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b))
    (hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant)
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (ξ : (pins F Φ).Z →* ℂˣ)
    (haesm : ∀ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v →
      AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 F) F))
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u)
    (y : AdelicGL2 (𝓞 F) F) (z : (pins F Φ).Z)
    (hz : NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ 2 =
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)) :
    IsAutomorphicFnAt F (pins F Φ) ξ (fun g => u (g * y)) ∧
      ∫⁻ g in Φ, ‖u (g * y)‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        ENNReal.ofReal (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2) * ∫⁻ g in Φ, ‖u g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := hright
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have huL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ u hu
  have huM := memLp_of_isAutomorphicFnAt F Φ ξ u hu
  have hFD1 := isFundamentalDomain_image_mul_right F d₁ d₂ Φ hslab hright hΦ y
  have hFD2 := isFundamentalDomain_image_centralScalar_mul F d₁ d₂ Φ hslab hright hΦ
    (z : (AdeleRing (𝓞 F) F)ˣ)
  rw [hz] at hFD2
  have hA1 := image_mul_right_subset_slab F d₁ d₂ Φ hΦs y
  have hA2 := image_centralScalar_mul_subset_slab F d₁ d₂ Φ hΦs (z : (AdeleRing (𝓞 F) F)ˣ)
  rw [hz] at hA2
  haveI := hinv (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
    (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
  have hEmbR : MeasurableEmbedding (fun g : AdelicGL2 (𝓞 F) F => g * y) :=
    (MeasurableEquiv.mulRight y).measurableEmbedding
  have hEmbL : MeasurableEmbedding
      (fun g : AdelicGL2 (𝓞 F) F => centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) :=
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ))).measurableEmbedding
  have hinvsq := smul_invariant_enorm_sq F Φ ξ u huL
  have hξe : ∀ g : AdelicGL2 (𝓞 F) F,
      ‖u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)‖ₑ ^ 2 =
        ENNReal.ofReal (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2) * ‖u g‖ₑ ^ 2 := by
    intro g
    rw [huL.central_transform z g, enorm_mul, mul_pow, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]

  have hlin : ∫⁻ g in Φ, ‖u (g * y)‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ENNReal.ofReal (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2) * ∫⁻ g in Φ, ‖u g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    calc ∫⁻ g in Φ, ‖u (g * y)‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∫⁻ g in (· * y) '' Φ, ‖u g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          (measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) y).setLIntegral_comp_emb hEmbR
            (fun g => ‖u g‖ₑ ^ 2) Φ
      _ = ∫⁻ g in (· * y) '' Φ, ‖u g‖ₑ ^ 2
            ∂(slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
              (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))) := by
          simp only [slabHaar, Measure.restrict_restrict_of_subset hA1]
      _ = ∫⁻ g in (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * ·) '' Φ, ‖u g‖ₑ ^ 2
            ∂(slabHaar F (d₁ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))
              (d₂ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y))) :=
          hFD1.setLIntegral_eq hFD2 _ hinvsq
      _ = ∫⁻ g in (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * ·) '' Φ, ‖u g‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          simp only [slabHaar, Measure.restrict_restrict_of_subset hA2]
      _ = ∫⁻ g in Φ, ‖u (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          ((measurePreserving_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F) _).setLIntegral_comp_emb hEmbL
            (fun g => ‖u g‖ₑ ^ 2) Φ).symm
      _ = ∫⁻ g in Φ, ENNReal.ofReal (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2) * ‖u g‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by simp only [hξe]
      _ = ENNReal.ofReal (‖((ξ z : ℂˣ) : ℂ)‖ ^ 2) * ∫⁻ g in Φ, ‖u g‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine ⟨?_, hlin⟩

  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨?_, ?_⟩ ?_
  · intro γ g
    show u (globalPoints (𝓞 F) F γ * g * y) = u (g * y)
    rw [mul_assoc, huL.left_invariant]
  · intro z' g
    show u (centralScalar (𝓞 F) F (z' : (AdeleRing (𝓞 F) F)ˣ) * g * y) = ((ξ z' : ℂˣ) : ℂ) * u (g * y)
    rw [mul_assoc, huL.central_transform]
  ·
    have hsm : AEStronglyMeasurable (fun g => u (g * y)) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
      ((haesm u hu).comp_measurePreserving
        (measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) y)).restrict
    refine ⟨hsm, ?_⟩
    have h2 : ∫⁻ g in Φ, ‖u g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).1
        huM.eLpNorm_lt_top
      simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using this
    refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).2 ?_
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [hlin]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2

private theorem ae_constantTerm_comp_mul_right_eq_zero
    (Φ : Set (AdelicGL2 (𝓞 F) F)) (hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant)
    (u : AdelicGL2 (𝓞 F) F → ℂ)
    (hu : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0)
    (y : AdelicGL2 (𝓞 F) F) :
    ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 (fun g => u (g * y)) g = 0 := by
  haveI := hright
  have hmp : MeasurePreserving (· * y) (adelicGLHaar (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 F) F) y
  have hq : Measure.QuasiMeasurePreserving (· * y) (adelicGLHaar (Fin 2) (𝓞 F) F)
      (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hmp.quasiMeasurePreserving
  have h1 := hq.ae (p := fun g => constantTerm (pins F Φ).ν unipotentGL2 u g = 0) hu
  filter_upwards [h1] with g hg
  have hg' : constantTerm (pins F Φ).ν unipotentGL2 u (g * y) = 0 := hg
  simpa only [constantTerm, constantTermIntegrand, mul_assoc] using hg'

section Hilbert

variable (Φ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pins F Φ).Z →* ℂˣ)

private def CuspAE (v : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v g = 0

private theorem cuspAE_congr {v w : AdelicGL2 (𝓞 F) F → ℂ} (h : v = w) (hv : CuspAE F Φ v) : CuspAE F Φ w :=
  h ▸ hv

private def HCTlin : Prop :=
  ∀ (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ) (c₁ c₂ : ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v₁ →
    IsAutomorphicFnAt F (pins F Φ) ξ v₂ → CuspAE F Φ v₁ → CuspAE F Φ v₂ →
    CuspAE F Φ (fun g => c₁ * v₁ g + c₂ * v₂ g)

private def HComplete : Prop :=
  ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
    (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) →
    Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0) →
    ∃ U, IsAutomorphicFnAt F (pins F Φ) ξ U ∧ U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v

private def HClosed : Prop :=
  ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
    (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) → (∀ n, CuspAE F Φ (useq n)) →
    IsAutomorphicFnAt F (pins F Φ) ξ v →
    Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0) →
    CuspAE F Φ v

private theorem isAutomorphicFnAt_zero : IsAutomorphicFnAt F (pins F Φ) ξ 0 :=
  isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ 0
    ⟨fun _ _ => rfl, fun _ _ => by simp only [Pi.zero_apply, mul_zero]⟩ MemLp.zero'

private theorem isAutomorphicFnAt_add (v w : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pins F Φ) ξ w) : IsAutomorphicFnAt F (pins F Φ) ξ (v + w) := by
  have hvL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ v hv
  have hwL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ w hw
  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨fun γ g => ?_, fun z g => ?_⟩
    ((memLp_of_isAutomorphicFnAt F Φ ξ v hv).add (memLp_of_isAutomorphicFnAt F Φ ξ w hw))
  · simp only [Pi.add_apply, hvL.left_invariant, hwL.left_invariant]
  · simp only [Pi.add_apply, hvL.central_transform, hwL.central_transform, mul_add]

private theorem isAutomorphicFnAt_smul (c : ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v) :
    IsAutomorphicFnAt F (pins F Φ) ξ (c • v) := by
  have hvL := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ v hv
  refine isAutomorphicFnAt_of_isLsXiFunction_of_memLp F Φ ξ _ ⟨fun γ g => ?_, fun z g => ?_⟩
    ((memLp_of_isAutomorphicFnAt F Φ ξ v hv).const_smul c)
  · simp only [Pi.smul_apply, hvL.left_invariant]
  · simp only [Pi.smul_apply, hvL.central_transform, smul_eq_mul]
    ring

private theorem isAutomorphicFnAt_sub (v w : AdelicGL2 (𝓞 F) F → ℂ) (hv : IsAutomorphicFnAt F (pins F Φ) ξ v)
    (hw : IsAutomorphicFnAt F (pins F Φ) ξ w) : IsAutomorphicFnAt F (pins F Φ) ξ (v - w) := by
  have h := isAutomorphicFnAt_add F Φ ξ v ((-1 : ℂ) • w) hv (isAutomorphicFnAt_smul F Φ ξ (-1) w hw)
  have heq : v + (-1 : ℂ) • w = v - w := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [heq] at h
  exact h

private theorem inner_eq_setIntegral (φ ψ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
    (v w : AdelicGL2 (𝓞 F) F → ℂ)
    (hv : (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v)
    (hw : (ψ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] w) :
    inner ℂ ψ φ = ∫ g in Φ, v g * (starRingEnd ℂ) (w g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv, hw] with g hgv hgw
  rw [RCLike.inner_apply, hgv, hgw]

private def cuspSubmodule (hCTlin : HCTlin F Φ ξ) :
    Submodule ℂ (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) where
  carrier := {φ | ∃ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v ∧ CuspAE F Φ v ∧
    (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v}
  zero_mem' := ⟨0, isAutomorphicFnAt_zero F Φ ξ,
    Filter.Eventually.of_forall fun g => by simp [constantTerm, constantTermIntegrand], Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro φ ψ ⟨v, hv, hvc, hφv⟩ ⟨w, hw, hwc, hψw⟩
    refine ⟨v + w, isAutomorphicFnAt_add F Φ ξ v w hv hw, ?_, (Lp.coeFn_add φ ψ).trans (hφv.add hψw)⟩
    have h := hCTlin v w 1 1 hv hw hvc hwc
    have heq : (fun g => (1 : ℂ) * v g + 1 * w g) = v + w := by funext g; simp only [one_mul, Pi.add_apply]
    rw [heq] at h
    exact h
  smul_mem' := by
    rintro c φ ⟨v, hv, hvc, hφv⟩
    refine ⟨c • v, isAutomorphicFnAt_smul F Φ ξ c v hv, ?_,
      (Lp.coeFn_smul c φ).trans (hφv.mono fun g hg => by simp only [Pi.smul_apply, hg])⟩
    have h := hCTlin v v c 0 hv hv hvc hvc
    have heq : (fun g => c * v g + 0 * v g) = c • v := by
      funext g; simp only [zero_mul, add_zero, Pi.smul_apply, smul_eq_mul]
    rw [heq] at h
    exact h

private theorem mem_cuspSubmodule_iff (hCTlin : HCTlin F Φ ξ)
    (φ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) :
    φ ∈ cuspSubmodule F Φ ξ hCTlin ↔ ∃ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v ∧
      CuspAE F Φ v ∧ (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v :=
  Iff.rfl

private theorem isClosed_cuspSubmodule
    (hcomplete : HComplete F Φ ξ) (hclosed : HClosed F Φ ξ) (hCTlin : HCTlin F Φ ξ) :
    IsClosed (cuspSubmodule F Φ ξ hCTlin : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) := by
  refine IsSeqClosed.isClosed ?_
  intro x xlim hx hconv
  have hx' : ∀ n, ∃ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v ∧ CuspAE F Φ v ∧
      ((x n : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v :=
    fun n => hx n
  choose v hv hvc hxv using hx'
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' x xlim).1 hconv
  have h2 : Filter.Tendsto (fun n => eLpNorm (v n - (xlim : AdelicGL2 (𝓞 F) F → ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 h1
    exact eLpNorm_congr_ae ((hxv n).sub Filter.EventuallyEq.rfl)
  obtain ⟨U, hU, hUx⟩ := hcomplete v xlim hv (Lp.memLp xlim) h2
  have h3 : Filter.Tendsto (fun n => eLpNorm (v n - U) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
      Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 h2
    exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hUx.symm)
  exact ⟨U, hU, hclosed v U hv hvc hU h3, hUx.symm⟩

private def resSubmodule : Submodule ℂ (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) where
  carrier := {φ | ∃ r : AdelicGL2 (𝓞 F) F → ℂ, r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧
    IsAutomorphicFnAt F (pins F Φ) ξ r ∧
    (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] r}
  zero_mem' := ⟨0, Submodule.zero_mem _, isAutomorphicFnAt_zero F Φ ξ, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro φ ψ ⟨r, hr, hra, hφr⟩ ⟨s, hs, hsa, hψs⟩
    exact ⟨r + s, Submodule.add_mem _ hr hs, isAutomorphicFnAt_add F Φ ξ r s hra hsa,
      (Lp.coeFn_add φ ψ).trans (hφr.add hψs)⟩
  smul_mem' := by
    rintro c φ ⟨r, hr, hra, hφr⟩
    exact ⟨c • r, Submodule.smul_mem _ c hr, isAutomorphicFnAt_smul F Φ ξ c r hra,
      (Lp.coeFn_smul c φ).trans (hφr.mono fun g hg => by simp only [Pi.smul_apply, hg])⟩

private theorem mem_resSubmodule_iff (φ : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) :
    φ ∈ resSubmodule F Φ ξ ↔ ∃ r : AdelicGL2 (𝓞 F) F → ℂ, r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧
      IsAutomorphicFnAt F (pins F Φ) ξ r ∧
      (φ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] r :=
  Iff.rfl

end Hilbert

private theorem setIntegral_mul_conj_chiDet_eq_zero_of_ae_constantTerm_eq_zero
    (d₁ d₂ : ℝ) (_hd : d₁ < d₂) (Φ : Set (AdelicGL2 (𝓞 F) F)) (hΦs : Φ ⊆ slab F d₁ d₂)
    [Countable (Γ F)] [MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F)]
    [MeasurableMul₂ (AdelicGL2 (𝓞 F) F)] [MeasurableInv (AdelicGL2 (𝓞 F) F)]
    [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F)]
    (hslab : ∀ a b : ℝ, MeasurableSet (slab F a b))
    (hinv : ∀ a b : ℝ, SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b))
    (hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant)
    (hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (hnorm : ∀ t : ℝ, 0 < t → ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = t)
    (ξ : (pins F Φ).Z →* ℂˣ)
    (haesm : ∀ v : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ v →
      AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 F) F))
    (htile : ∀ P : AdelicGL2 (𝓞 F) F → Prop,
      (∀ (γ : Γ F) (g : AdelicGL2 (𝓞 F) F), P ((γ : AdelicGL2 (𝓞 F) F) * g) ↔ P g) →
      (∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ), P g) → ∀ᵐ g ∂(slabHaar F d₁ d₂), P g)
    (hdescend : ∀ P : AdelicGL2 (𝓞 F) F → Prop,
      (∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ (pins F Φ).Z → ∀ g : AdelicGL2 (𝓞 F) F,
        P (centralScalar (𝓞 F) F w * g) → P g) →
      (∀ᵐ g ∂(slabHaar F d₁ d₂), P g) → ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), P g)
    (hergodic : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, AEStronglyMeasurable ψ (adelicGLHaar (Fin 2) (𝓞 F) F) →
      (∀ y : AdelicGL2 (𝓞 F) F, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ψ (g * y) = ψ g) →
      ∃ c : ℂ, ψ =ᵐ[adelicGLHaar (Fin 2) (𝓞 F) F] fun _ => c)
    (hcomplete : ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
      MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) →
      Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
        Filter.atTop (nhds 0) →
      ∃ U, IsAutomorphicFnAt F (pins F Φ) ξ U ∧ U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v)
    (hclosed : ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
      (∀ n, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 (useq n) g = 0) →
      IsAutomorphicFnAt F (pins F Φ) ξ v →
      Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
        Filter.atTop (nhds 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v g = 0)
    (hCTae : ∀ (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v₁ →
      IsAutomorphicFnAt F (pins F Φ) ξ v₂ → v₁ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v₂ →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0)
    (hCTlin : ∀ (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ) (c₁ c₂ : ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v₁ →
      IsAutomorphicFnAt F (pins F Φ) ξ v₂ →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0) →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
        constantTerm (pins F Φ).ν unipotentGL2 (fun g => c₁ * v₁ g + c₂ * v₂ g) g = 0)
    (u : AdelicGL2 (𝓞 F) F → ℂ) (hu : IsAutomorphicFnAt F (pins F Φ) ξ u)
    (hcusp : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 u g = 0)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsAutomorphicFnAt F (pins F Φ) ξ (chiDet (𝓞 F) F χ)) :
    ∫ g in Φ, u g * (starRingEnd ℂ) (chiDet (𝓞 F) F χ g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := by
  haveI := hright
  haveI : IsProbabilityMeasure (pins F Φ).ν := isProbabilityMeasure_cond_adelicBox F

  let K := cuspSubmodule F Φ ξ hCTlin
  have hKc : IsClosed (K : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) :=
    isClosed_cuspSubmodule F Φ ξ hcomplete hclosed hCTlin
  haveI : CompleteSpace K := hKc.completeSpace_coe
  have hrM := memLp_of_isAutomorphicFnAt F Φ ξ _ hχ
  let rL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hrM.toLp (chiDet (𝓞 F) F χ)
  have hrL : (rL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] chiDet (𝓞 F) F χ :=
    hrM.coeFn_toLp
  let a : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := ↑(K.orthogonalProjection rL)
  have haK : a ∈ K := (K.orthogonalProjection rL).2
  have hraK : rL - a ∈ Kᗮ := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := K) rL
    rwa [Submodule.starProjection_apply] at h
  obtain ⟨a₀, ha₀, ha₀c, haa₀⟩ := (K.orthogonalProjection rL).2
  have ha₀L := isLsXiFunction_of_isAutomorphicFnAt F Φ ξ a₀ ha₀
  have hra₀ : ((rL - a : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) : AdelicGL2 (𝓞 F) F → ℂ)
      =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] (chiDet (𝓞 F) F χ - a₀) :=
    (Lp.coeFn_sub _ _).trans (hrL.sub haa₀)

  suffices hzero : a₀ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] 0 by
    have huM := memLp_of_isAutomorphicFnAt F Φ ξ u hu
    let uL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := huM.toLp u
    have huL : (uL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] u := huM.coeFn_toLp
    have huK : uL ∈ K := ⟨u, hu, hcusp, huL⟩
    have ha0 : a = 0 := Lp.ext ((haa₀.trans hzero).trans (Lp.coeFn_zero _ _ _).symm)
    have hrK : rL ∈ Kᗮ := by simpa only [ha0, sub_zero] using hraK
    have h := Submodule.inner_right_of_mem_orthogonal huK hrK
    rw [inner_eq_setIntegral F Φ rL uL (chiDet (𝓞 F) F χ) u hrL huL] at h
    have h2 : ∫ g in Φ, u g * (starRingEnd ℂ) (chiDet (𝓞 F) F χ g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        (starRingEnd ℂ) (∫ g in Φ, chiDet (𝓞 F) F χ g * (starRingEnd ℂ) (u g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) := by
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [map_mul, starRingEnd_self_apply, mul_comm]
    rw [h2, h, map_zero]

  have hcov : ∀ y : AdelicGL2 (𝓞 F) F, ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ),
      a₀ (g * y) = chiDet (𝓞 F) F χ y * a₀ g := by
    intro y
    have hcy : chiDet (𝓞 F) F χ y ≠ 0 := chiDet_ne_zero F χ y

    obtain ⟨z₀, hz₀⟩ := hnorm (Real.sqrt (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y)))
      (Real.sqrt_pos.2 (NumberField.TateGlobal.ideleNorm_pos _))
    let z : (pins F Φ).Z := ⟨z₀, show z₀ ∈ (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) from Subgroup.mem_top z₀⟩
    have hz : NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ 2 =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) := by
      show NumberField.TateGlobal.ideleNorm F z₀ ^ 2 = _
      rw [hz₀, Real.sq_sqrt (NumberField.TateGlobal.ideleNorm_pos _).le]
    have hz' : NumberField.TateGlobal.ideleNorm F ((z⁻¹ : (pins F Φ).Z) : (AdeleRing (𝓞 F) F)ˣ) ^ 2 =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y⁻¹) := by
      rw [Subgroup.coe_inv, ideleNorm_inv', map_inv, ideleNorm_inv', inv_pow, hz]

    obtain ⟨hty, -⟩ :=
      isAutomorphicFnAt_comp_mul_right F d₁ d₂ Φ hΦs hslab hinv hright hΦ ξ haesm a₀ ha₀ y z hz
    have htyc := ae_constantTerm_comp_mul_right_eq_zero F Φ hright a₀ ha₀c y
    have hay : IsAutomorphicFnAt F (pins F Φ) ξ ((chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) :=
      isAutomorphicFnAt_smul F Φ ξ _ _ hty
    have hayc : CuspAE F Φ ((chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) := by
      have hF : (fun g => (chiDet (𝓞 F) F χ y)⁻¹ * a₀ (g * y) + 0 * a₀ (g * y)) =
          (chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y) := by
        funext g; simp only [zero_mul, add_zero, Pi.smul_apply, smul_eq_mul]
      exact cuspAE_congr F Φ hF (hCTlin _ _ (chiDet (𝓞 F) F χ y)⁻¹ 0 hty hty htyc htyc)
    have hayM := memLp_of_isAutomorphicFnAt F Φ ξ _ hay
    let ayL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
      hayM.toLp ((chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y))
    have hayL : (ayL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ]
        ((chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) := hayM.coeFn_toLp
    have hayK : ayL ∈ K := ⟨_, hay, hayc, hayL⟩

    have hD : IsAutomorphicFnAt F (pins F Φ) ξ (chiDet (𝓞 F) F χ - a₀) := isAutomorphicFnAt_sub F Φ ξ _ _ hχ ha₀
    have hrayK : rL - ayL ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro κ ⟨v, hv, hvc, hκv⟩
      have hray : ((rL - ayL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) : AdelicGL2 (𝓞 F) F → ℂ)
          =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ]
            (chiDet (𝓞 F) F χ - (chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) :=
        (Lp.coeFn_sub _ _).trans (hrL.sub hayL)
      rw [inner_eq_setIntegral F Φ (rL - ayL) κ _ v hray hκv]
      have hpt : ∀ g : AdelicGL2 (𝓞 F) F,
          (chiDet (𝓞 F) F χ - (chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) g * (starRingEnd ℂ) (v g) =
            (chiDet (𝓞 F) F χ y)⁻¹ * ((chiDet (𝓞 F) F χ - a₀) (g * y) * (starRingEnd ℂ) (v g)) := by
        intro g
        have e1 : (chiDet (𝓞 F) F χ - (chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) g =
            chiDet (𝓞 F) F χ g - (chiDet (𝓞 F) F χ y)⁻¹ * a₀ (g * y) := rfl
        have e2 : (chiDet (𝓞 F) F χ - a₀) (g * y) = chiDet (𝓞 F) F χ g * chiDet (𝓞 F) F χ y - a₀ (g * y) := by
          rw [Pi.sub_apply, chiDet_mul]
        have e3 : (chiDet (𝓞 F) F χ y)⁻¹ * (chiDet (𝓞 F) F χ g * chiDet (𝓞 F) F χ y) = chiDet (𝓞 F) F χ g := by
          rw [mul_comm (chiDet (𝓞 F) F χ g), ← mul_assoc, inv_mul_cancel₀ hcy, one_mul]
        rw [e1, e2]
        calc (chiDet (𝓞 F) F χ g - (chiDet (𝓞 F) F χ y)⁻¹ * a₀ (g * y)) * (starRingEnd ℂ) (v g)
            = ((chiDet (𝓞 F) F χ y)⁻¹ * (chiDet (𝓞 F) F χ g * chiDet (𝓞 F) F χ y)
                - (chiDet (𝓞 F) F χ y)⁻¹ * a₀ (g * y)) *
                (starRingEnd ℂ) (v g) := by rw [e3]
          _ = _ := by ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
        setIntegral_comp_mul_right_mul_conj_eq F d₁ d₂ Φ hΦs hslab hinv hright hΦ ξ _ v hD hv y z hz]

      obtain ⟨hvy, -⟩ :=
        isAutomorphicFnAt_comp_mul_right F d₁ d₂ Φ hΦs hslab hinv hright hΦ ξ haesm v hv y⁻¹ z⁻¹ hz'
      have hvyc := ae_constantTerm_comp_mul_right_eq_zero F Φ hright v hvc y⁻¹
      have hvyM := memLp_of_isAutomorphicFnAt F Φ ξ _ hvy
      let vyL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hvyM.toLp (fun g => v (g * y⁻¹))
      have hvyL : (vyL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] fun g => v (g * y⁻¹) :=
        hvyM.coeFn_toLp
      have hvyK : vyL ∈ K := ⟨_, hvy, hvyc, hvyL⟩
      have h0 := Submodule.inner_right_of_mem_orthogonal hvyK hraK
      rw [inner_eq_setIntegral F Φ (rL - a) vyL (chiDet (𝓞 F) F χ - a₀) _ hra₀ hvyL] at h0
      rw [h0, mul_zero, mul_zero]

    have hd1 : a - ayL ∈ K := K.sub_mem haK hayK
    have hd2 : a - ayL ∈ Kᗮ := by
      have h : rL - ayL - (rL - a) ∈ Kᗮ := Submodule.sub_mem Kᗮ hrayK hraK
      rwa [sub_sub_sub_cancel_left] at h
    have hd : a - ayL = 0 := inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hd1 hd2)
    have hae : a = ayL := sub_eq_zero.1 hd
    have hcoe : ∀ g : AdelicGL2 (𝓞 F) F, (a : AdelicGL2 (𝓞 F) F → ℂ) g = (ayL : AdelicGL2 (𝓞 F) F → ℂ) g :=
      fun g => by rw [hae]
    filter_upwards [haa₀, hayL] with g h1 h2
    have h3 := hcoe g
    have h4 : a₀ g = (chiDet (𝓞 F) F χ y)⁻¹ * a₀ (g * y) := by
      have h5 : a₀ g = ((chiDet (𝓞 F) F χ y)⁻¹ • fun g => a₀ (g * y)) g := h1.symm.trans (h3.trans h2)
      simpa only [Pi.smul_apply, smul_eq_mul] using h5
    rw [h4, ← mul_assoc, mul_inv_cancel₀ hcy, one_mul]

  have hcovG : ∀ y : AdelicGL2 (𝓞 F) F, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      a₀ (g * y) = chiDet (𝓞 F) F χ y * a₀ g := by
    intro y
    refine hdescend (fun g => a₀ (g * y) = chiDet (𝓞 F) F χ y * a₀ g) ?_ (htile _ ?_ (hcov y))
    · intro w hw g hP
      have hP' : a₀ (centralScalar (𝓞 F) F w * g * y) = chiDet (𝓞 F) F χ y * a₀ (centralScalar (𝓞 F) F w * g) := hP
      have e1 : a₀ (centralScalar (𝓞 F) F w * g * y) = ((ξ ⟨w, hw⟩ : ℂˣ) : ℂ) * a₀ (g * y) := by
        rw [mul_assoc]; exact ha₀L.central_transform ⟨w, hw⟩ (g * y)
      have e2 : a₀ (centralScalar (𝓞 F) F w * g) = ((ξ ⟨w, hw⟩ : ℂˣ) : ℂ) * a₀ g :=
        ha₀L.central_transform ⟨w, hw⟩ g
      have h3 : ((ξ ⟨w, hw⟩ : ℂˣ) : ℂ) * a₀ (g * y) = ((ξ ⟨w, hw⟩ : ℂˣ) : ℂ) * (chiDet (𝓞 F) F χ y * a₀ g) := by
        rw [← e1, hP', e2]; ring
      exact mul_left_cancel₀ (Units.ne_zero _) h3
    · intro γ g
      obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.1 γ.2
      show a₀ ((γ : AdelicGL2 (𝓞 F) F) * g * y) = chiDet (𝓞 F) F χ y * a₀ ((γ : AdelicGL2 (𝓞 F) F) * g) ↔
        a₀ (g * y) = chiDet (𝓞 F) F χ y * a₀ g
      rw [← hγ₀, mul_assoc, ha₀L.left_invariant, ha₀L.left_invariant]

  obtain ⟨c, hc⟩ := hergodic (fun g => a₀ g * (chiDet (𝓞 F) F χ g)⁻¹)
    (((haesm a₀ ha₀).aemeasurable.mul (haesm _ hχ).aemeasurable.inv).aestronglyMeasurable) (by
      intro y
      filter_upwards [hcovG y] with g hg
      show a₀ (g * y) * (chiDet (𝓞 F) F χ (g * y))⁻¹ = a₀ g * (chiDet (𝓞 F) F χ g)⁻¹
      rw [hg, chiDet_mul, mul_inv]
      calc chiDet (𝓞 F) F χ y * a₀ g * ((chiDet (𝓞 F) F χ g)⁻¹ * (chiDet (𝓞 F) F χ y)⁻¹)
          = a₀ g * (chiDet (𝓞 F) F χ g)⁻¹ * (chiDet (𝓞 F) F χ y * (chiDet (𝓞 F) F χ y)⁻¹) := by ring
        _ = a₀ g * (chiDet (𝓞 F) F χ g)⁻¹ := by rw [mul_inv_cancel₀ (chiDet_ne_zero F χ y), mul_one])
  have hac : a₀ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F)] (c • chiDet (𝓞 F) F χ) := by
    filter_upwards [hc] with g hg
    have hg' : a₀ g * (chiDet (𝓞 F) F χ g)⁻¹ = c := hg
    rw [Pi.smul_apply, smul_eq_mul, ← hg', mul_assoc, inv_mul_cancel₀ (chiDet_ne_zero F χ g), mul_one]

  have hcr : IsAutomorphicFnAt F (pins F Φ) ξ (c • chiDet (𝓞 F) F χ) := isAutomorphicFnAt_smul F Φ ξ c _ hχ
  have hcc : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
      constantTerm (pins F Φ).ν unipotentGL2 (c • chiDet (𝓞 F) F χ) g = 0 :=
    hCTae a₀ _ ha₀ hcr (ae_restrict_of_ae hac) ha₀c
  have hCT : ∀ g : AdelicGL2 (𝓞 F) F,
      constantTerm (pins F Φ).ν unipotentGL2 (c • chiDet (𝓞 F) F χ) g = c * chiDet (𝓞 F) F χ g := by
    intro g
    simp only [constantTerm, constantTermIntegrand, Pi.smul_apply, smul_eq_mul, chiDet_unipotentGL2_mul,
      integral_const, probReal_univ, one_smul]
  have hc0 : c = 0 := by
    haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
    obtain ⟨g, hg⟩ := hcc.exists
    rw [hCT] at hg
    exact (mul_eq_zero.1 hg).resolve_right (chiDet_ne_zero F χ g)
  refine ae_restrict_of_ae ?_
  filter_upwards [hac] with g hg
  rw [hg, Pi.smul_apply, hc0, zero_smul, Pi.zero_apply]

private theorem exists_threeWay_decomposition
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂) (Φ : Set (AdelicGL2 (𝓞 F) F)) (_hΦs : Φ ⊆ slab F d₁ d₂)
    (_hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂))
    (ξ : (pins F Φ).Z →* ℂˣ)
    (hcomplete : ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
      MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) →
      Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
        Filter.atTop (nhds 0) →
      ∃ U, IsAutomorphicFnAt F (pins F Φ) ξ U ∧ U =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v)
    (hclosed : ∀ (useq : ℕ → AdelicGL2 (𝓞 F) F → ℂ) (v : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsAutomorphicFnAt F (pins F Φ) ξ (useq n)) →
      (∀ n, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 (useq n) g = 0) →
      IsAutomorphicFnAt F (pins F Φ) ξ v →
      Filter.Tendsto (fun n => eLpNorm (useq n - v) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))
        Filter.atTop (nhds 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v g = 0)
    (hCTae : ∀ (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v₁ →
      IsAutomorphicFnAt F (pins F Φ) ξ v₂ → v₁ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v₂ →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0)
    (hCTlin : ∀ (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ) (c₁ c₂ : ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v₁ →
      IsAutomorphicFnAt F (pins F Φ) ξ v₂ →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₁ g = 0) →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v₂ g = 0) →
      ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F),
        constantTerm (pins F Φ).ν unipotentGL2 (fun g => c₁ * v₁ g + c₂ * v₂ g) g = 0)
    (horth : ∀ (v : AdelicGL2 (𝓞 F) F → ℂ), IsAutomorphicFnAt F (pins F Φ) ξ v →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 v g = 0) →
      ∀ (h : AdelicGL2 (𝓞 F) F → ℂ), IsAutomorphicFnAt F (pins F Φ) ξ h →
      h ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ →
      ∫ g in Φ, v g * (starRingEnd ℂ) (h g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsAutomorphicFnAt F (pins F Φ) ξ f) :
    ∃ fc fr fe : AdelicGL2 (𝓞 F) F → ℂ,
      (IsAutomorphicFnAt F (pins F Φ) ξ fc
          ∧ (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 fc g = 0))
      ∧ (IsAutomorphicFnAt F (pins F Φ) ξ fr
          ∧ ∀ ε : ℝ, 0 < ε → ∃ r : AdelicGL2 (𝓞 F) F → ℂ,
              r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧ IsAutomorphicFnAt F (pins F Φ) ξ r
                ∧ eLpNorm (fr - r) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) < ENNReal.ofReal ε)
      ∧ (IsAutomorphicFnAt F (pins F Φ) ξ fe
          ∧ ∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsAutomorphicFnAt F (pins F Φ) ξ h →
              ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), constantTerm (pins F Φ).ν unipotentGL2 h g = 0)
                ∨ h ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ) →
              ∫ g in Φ, fe g * (starRingEnd ℂ) (h g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0)
      ∧ f =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] fc + fr + fe := by
  have _ := hCTae

  let K := cuspSubmodule F Φ ξ hCTlin
  have hKc : IsClosed (K : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) :=
    isClosed_cuspSubmodule F Φ ξ hcomplete hclosed hCTlin
  haveI : CompleteSpace K := hKc.completeSpace_coe
  let B := (resSubmodule F Φ ξ).topologicalClosure
  haveI : CompleteSpace B := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  have hBK : B ≤ Kᗮ := by
    refine Submodule.topologicalClosure_minimal _ (fun ψ hψ => ?_) (Submodule.isClosed_orthogonal _)
    obtain ⟨r, hr, hra, hψr⟩ := hψ
    rw [Submodule.mem_orthogonal']
    rintro κ ⟨v, hv, hvc, hκv⟩
    rw [inner_eq_setIntegral F Φ κ ψ v r hκv hψr]
    exact horth v hv hvc r hra hr

  have hfM := memLp_of_isAutomorphicFnAt F Φ ξ f hf
  let fL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hfM.toLp f
  have hfL : (fL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] f := hfM.coeFn_toLp
  let a : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := ↑(K.orthogonalProjection fL)
  have haK : a ∈ K := (K.orthogonalProjection fL).2
  have haK' : fL - a ∈ Kᗮ := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := K) fL
    rwa [Submodule.starProjection_apply] at h
  obtain ⟨fc, hfc, hfcc, hafc⟩ := haK
  let b : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := ↑(B.orthogonalProjection (fL - a))
  have hbB : b ∈ B := (B.orthogonalProjection (fL - a)).2
  have hbB' : (fL - a) - b ∈ Bᗮ := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := B) (fL - a)
    rwa [Submodule.starProjection_apply] at h

  have hbcl : b ∈ closure (resSubmodule F Φ ξ : Set (Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ))) := by
    rw [← Submodule.topologicalClosure_coe]; exact hbB
  obtain ⟨ψ, hψ, hψb⟩ := mem_closure_iff_seq_limit.1 hbcl
  have hψ' : ∀ n, ∃ r : AdelicGL2 (𝓞 F) F → ℂ, r ∈ residualSpan (𝓞 F) F (pins F Φ).Z ξ ∧
      IsAutomorphicFnAt F (pins F Φ) ξ r ∧
      ((ψ n : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] r :=
    fun n => hψ n
  choose rseq hrs hra hψr using hψ'
  have hb1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' ψ b).1 hψb
  have hb2 : Filter.Tendsto (fun n => eLpNorm (rseq n - (b : AdelicGL2 (𝓞 F) F → ℂ)) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)) Filter.atTop (nhds 0) := by
    refine (Filter.tendsto_congr fun n => ?_).1 hb1
    exact eLpNorm_congr_ae ((hψr n).sub Filter.EventuallyEq.rfl)
  obtain ⟨fr, hfr, hbfr⟩ := hcomplete rseq b hra (Lp.memLp b) hb2

  refine ⟨fc, fr, f - fc - fr, ⟨hfc, hfcc⟩, ⟨hfr, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  ·
    intro ε hε
    obtain ⟨φ, hφ, hdist⟩ := Metric.mem_closure_iff.1 hbcl ε hε
    obtain ⟨r, hr, hrauto, hφr⟩ := hφ
    refine ⟨r, hr, hrauto, ?_⟩
    have hne : eLpNorm ((b : AdelicGL2 (𝓞 F) F → ℂ) - (φ : AdelicGL2 (𝓞 F) F → ℂ)) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) ≠ ⊤ := ((Lp.memLp b).sub (Lp.memLp φ)).eLpNorm_ne_top
    have heq : eLpNorm (fr - r) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) =
        eLpNorm ((b : AdelicGL2 (𝓞 F) F → ℂ) - (φ : AdelicGL2 (𝓞 F) F → ℂ)) 2
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) :=
      eLpNorm_congr_ae (hbfr.sub hφr.symm)
    rw [heq, ENNReal.lt_ofReal_iff_toReal_lt hne, ← Lp.dist_def]
    exact hdist
  ·
    exact isAutomorphicFnAt_sub F Φ ξ _ _ (isAutomorphicFnAt_sub F Φ ξ _ _ hf hfc) hfr
  ·
    intro h hh hhyp
    have hhM := memLp_of_isAutomorphicFnAt F Φ ξ h hh
    let hL : Lp ℂ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := hhM.toLp h
    have hhL : (hL : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] h := hhM.coeFn_toLp
    have hfeL : ((fL - a - b : Lp ℂ 2 _) : AdelicGL2 (𝓞 F) F → ℂ)
        =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] (f - fc - fr) :=
      (Lp.coeFn_sub _ _).trans (((Lp.coeFn_sub _ _).trans (hfL.sub hafc)).sub hbfr.symm)
    rw [← inner_eq_setIntegral F Φ (fL - a - b) hL (f - fc - fr) h hfeL hhL]
    rcases hhyp with hcusp | hres
    ·
      have hhK : hL ∈ K := ⟨h, hh, hcusp, hhL⟩
      have hmem : fL - a - b ∈ Kᗮ := Submodule.sub_mem _ haK' (hBK hbB)
      exact Submodule.inner_right_of_mem_orthogonal hhK hmem
    ·
      have hhB : hL ∈ B := Submodule.le_topologicalClosure _ ⟨h, hres, hh, hhL⟩
      exact Submodule.inner_right_of_mem_orthogonal hhB hbB'
  ·
    have hsum : fc + fr + (f - fc - fr) = f := by
      funext g
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    exact Filter.EventuallyEq.of_eq hsum.symm

end AutomorphicForm.LsXiOrthogonalSplit

end

end

section

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab.AutomorphicForm P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab.AutomorphicForm.LsXiOrthogonalSplit"
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (_hv : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ v) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI hright : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 F) F) := inferInstance
  haveI : MeasurableMul₂ (AdelicGL2 (𝓞 F) F) := inferInstance
  haveI : MeasurableInv (AdelicGL2 (𝓞 F) F) := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  haveI : Countable (Γ F) := countable_range_globalPoints F
  haveI : MeasurableConstSMul (Γ F) (AdelicGL2 (𝓞 F) F) := ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 F) F)⟩

  have hslab : ∀ a b : ℝ, MeasurableSet (slab F a b) :=
    fun a b => NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F a b
  have hinv : ∀ a b : ℝ, SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) (slabHaar F a b) := fun a b =>
    smulInvariantMeasure_slabHaar F a b (hslab a b) (fun x => AutomorphicForm.ideleNorm_det_globalPoints x)
  haveI := hinv d₁ d₂
  have hΦ : IsFundamentalDomain (Γ F) Φ (slabHaar F d₁ d₂) := _hΦ
  have hnorm : ∀ t : ℝ, 0 < t → ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = t := by
    intro t ht
    obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
    have hr0 : (0 : NNReal) < ⟨t, ht.le⟩ := by exact_mod_cast ht
    refine ⟨s (Units.mk0 ⟨t, ht.le⟩ hr0.ne'), ?_⟩
    exact (hs _).trans rfl
  have hcover : ∃ z : ℕ → (pins F Φ).Z, ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F), ∃ n,
      centralScalar (𝓞 F) F ((z n : (AdeleRing (𝓞 F) F)ˣ))⁻¹ * g ∈ slab F d₁ d₂ :=
    exists_central_cover_slab F d₁ d₂ _hd₁ _hd Φ hnorm
  exact aestronglyMeasurable_haar_of_isAutomorphicFnAt F d₁ d₂ Φ hΦ (hslab d₁ d₂) hcover ξ v _hv

end

end

end
end S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
end P2MW
export P2MW.S_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab (solution)
