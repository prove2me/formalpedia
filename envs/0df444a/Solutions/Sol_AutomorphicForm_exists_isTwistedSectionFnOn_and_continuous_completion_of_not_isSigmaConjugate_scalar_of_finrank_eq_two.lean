-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c853dc91-6227-5ede-8e98-8b2c7729379c

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
import Theorems.Thm_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
import Theorems.Thm_NumberField_InfinitePlace_nonempty_algHom_completion_of_isUnramified
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
import Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Ws46
namespace InvTC

section Aux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

theorem map_mul_right_eq_modularCharacter_smul (g : G) :
    Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
  rw [show Measure.modularCharacter g = Measure.modularCharacterFun g from rfl,
    Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact Measure.isMulLeftInvariant_eq_smul _ _

theorem modularCharacter_mul_measure_image (g : G) (A : Set G) :
    (Measure.modularCharacter g : ℝ≥0∞) * μ ((· * g) '' A) = μ A := by
  have h := congrArg (fun ν : Measure G => ν ((· * g) '' A)) (map_mul_right_eq_modularCharacter_smul μ g)
  simp only [Measure.coe_nnreal_smul_apply] at h
  rw [← h, show Measure.map (· * g) μ = Measure.map (Homeomorph.mulRight g).toMeasurableEquiv μ from rfl,
    MeasurableEquiv.map_apply]
  congr 1
  exact (Homeomorph.mulRight g).injective.preimage_image A

include μ in

theorem modularCharacter_eq_one_of_mem_center (z : G) (hz : z ∈ Subgroup.center G) :
    Measure.modularCharacter z = 1 := by
  have h := map_mul_right_eq_modularCharacter_smul μ z
  have hzc : (fun x : G => x * z) = fun x => z * x := by
    funext x; exact Subgroup.mem_center_iff.mp hz x
  rw [hzc, map_mul_left_eq_self] at h
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK1
  have hfin : μ K < ∞ := hK.measure_lt_top
  have hKeq := congrArg (fun ν : Measure G => ν K) h
  simp only [Measure.coe_nnreal_smul_apply] at hKeq
  have h1 : ((Measure.modularCharacter z : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
    exact hKeq.symm
  exact_mod_cast h1

end Aux

theorem isInvInvariant_of_isCompact_mul_center
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (C : Set G) (hC : IsCompact C)
    (hCZ : ∀ g : G, ∃ c ∈ C, ∃ z ∈ Subgroup.center G, g = c * z)
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant := by

  set Δ : G →* ℝ≥0 := Measure.modularCharacter with hΔ

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨c₀, hc₀, -⟩ := hCZ 1
  set A : Set G := K * C with hA
  set B : Set G := K * C * C with hB
  have hAc : IsCompact A := hK.mul hC
  have hBc : IsCompact B := (hK.mul hC).mul hC
  have hApos : 0 < μ A := by
    have hsub : (· * c₀) '' interior K ⊆ A := by
      rintro _ ⟨k, hk, rfl⟩
      exact Set.mul_mem_mul (interior_subset hk) hc₀
    have hopen : IsOpen ((· * c₀) '' interior K) := (Homeomorph.mulRight c₀).isOpenMap _ isOpen_interior
    have hne : ((· * c₀) '' interior K).Nonempty := ⟨1 * c₀, ⟨1, mem_interior_iff_mem_nhds.mpr hK1, rfl⟩⟩
    exact lt_of_lt_of_le (hopen.measure_pos μ hne) (measure_mono hsub)
  have hAfin : μ A < ∞ := hAc.measure_lt_top
  have hBfin : μ B < ∞ := hBc.measure_lt_top

  have hbound : ∀ g : G, μ A ≤ (Δ g : ℝ≥0∞) * μ B := by
    intro g
    obtain ⟨c, hc, z, hz, rfl⟩ := hCZ g
    rw [← modularCharacter_mul_measure_image μ (c * z) A]
    refine mul_le_mul_right ?_ _

    have hsub : (· * (c * z)) '' A ⊆ (fun x => z * x) '' B := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨a * c, Set.mul_mem_mul ha hc, ?_⟩
      show z * (a * c) = a * (c * z)
      rw [← mul_assoc a c z]
      exact (Subgroup.mem_center_iff.mp hz (a * c)).symm
    calc μ ((· * (c * z)) '' A) ≤ μ ((fun x => z * x) '' B) := measure_mono hsub
      _ = μ B := by rw [Set.image_mul_left, measure_preimage_mul]

  have hBpos : 0 < μ B := lt_of_lt_of_le hApos (le_trans (le_refl _) (by
    calc μ A ≤ (Δ 1 : ℝ≥0∞) * μ B := hbound 1
      _ = μ B := by rw [map_one, ENNReal.coe_one, one_mul]))
  set m : ℝ≥0 := (μ A).toNNReal / (μ B).toNNReal with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact div_pos (ENNReal.toNNReal_pos hApos.ne' hAfin.ne) (ENNReal.toNNReal_pos hBpos.ne' hBfin.ne)
  have hlow : ∀ g : G, m ≤ Δ g := by
    intro g
    have h := hbound g
    rw [← ENNReal.coe_toNNReal hAfin.ne, ← ENNReal.coe_toNNReal hBfin.ne, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h
    rw [hm, div_le_iff₀ (ENNReal.toNNReal_pos hBpos.ne' hBfin.ne)]
    exact h

  have hle : ∀ g : G, Δ g ≤ 1 := by
    intro g
    by_contra hgt
    push_neg at hgt

    have hinv : Δ g⁻¹ < 1 := by
      rw [map_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hmpos hinv
    have := hlow (g⁻¹ ^ n)
    rw [map_pow] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)
  have hone : ∀ g : G, Δ g = 1 := by
    intro g
    apply le_antisymm (hle g)
    have h := hle g⁻¹
    rw [map_inv] at h
    have hpos : 0 < Δ g := lt_of_lt_of_le hmpos (hlow g)
    rwa [inv_le_one₀ hpos] at h

  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [map_mul_right_eq_modularCharacter_smul μ g, show Measure.modularCharacter g = 1 from hone g, one_smul]⟩
  exact MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant μ

end Ws46.InvTC

open MeasureTheory NumberField AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace Ws46
namespace TsCent2

section Closed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h : Continuous (sigmaTensor K L A σ) := by
    have := IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
    exact this
  exact Continuous.units_map _ (continuous_id.matrix_map h)

theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed (twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul ((continuous_sigmaGL K L A σ).inv)
  have : (twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t; exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

theorem locallyCompactSpace_twistedCentralizer [T2Space A] [LocallyCompactSpace A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    LocallyCompactSpace (twistedCentralizer K L A σ δ) := by
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  exact (isClosed_twistedCentralizer K L A σ δ).isClosedEmbedding_subtypeVal.locallyCompactSpace

end Closed

section Generic

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

theorem isMulRightInvariant_of_isInvInvariant (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant] :
    μ.IsMulRightInvariant := by
  have h : μ.inv.IsMulRightInvariant := inferInstance
  rwa [Measure.inv_eq_self] at h

end Generic

section Model

attribute [local instance 10000] AutomorphicForm.glBorelOf

theorem secondCountableTopology_gl (R : Type) [CommRing R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

section Scalars
variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {A : Type} [CommRing A] [Algebra K A]

theorem scalar_mul_comm' (c : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : L ⊗[K] A) * (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * Matrix.scalar (Fin 2) (c : L ⊗[K] A)
  exact (Matrix.scalar_commute (c : L ⊗[K] A) (fun r => Commute.all _ r) _).eq

theorem scalar_includeRight (z : Aˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom z) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  apply Units.ext; ext i j
  show (Matrix.scalar (Fin 2) _) i j =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((Matrix.scalar (Fin 2) (z : A)) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact (map_zero _).symm

theorem toTensorGL_scalar_mul_comm (e : Aˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) e) * g = g * toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) e) := by
  rw [← scalar_includeRight, scalar_mul_comm']

end Scalars

theorem exists_isTwistedSectionFnOn_conjAe_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφc : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ' φ W ∧ Continuous W := by

  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := AutomorphicForm.t2Space_tensorGL ℝ ℂ ℝ
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL ℝ ℂ ℝ
  haveI : SecondCountableTopology (ℂ ⊗[ℝ] ℝ) := Module.Finite.secondCountabletopology ℝ (ℂ ⊗[ℝ] ℝ)
  haveI : SecondCountableTopology (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := secondCountableTopology_gl _
  haveI := AutomorphicForm.borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)

  set T := twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ with hT
  have hTc : IsClosed (T : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) := isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
  haveI : LocallyCompactSpace T := locallyCompactSpace_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
  letI : MeasurableSpace T := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : τ'.IsHaarMeasure := hτ'
  haveI : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology _
  have hι : Topology.IsClosedEmbedding (T.subtype : T → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := hTc.isClosedEmbedding_subtypeVal

  obtain ⟨C, hC, hCT, hdec⟩ :=
    AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg c hc δ y hδ
  have hC' : IsCompact ((Subtype.val : T → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) ⁻¹' C) := hι.isCompact_preimage hC
  haveI : τ'.IsInvInvariant := by
    refine Ws46.InvTC.isInvInvariant_of_isCompact_mul_center ((Subtype.val : T → _) ⁻¹' C) hC' (fun g => ?_) τ'
    obtain ⟨e, k, hk, hgk⟩ := hdec g g.2
    have hkT : k ∈ T := hCT hk
    have hzT : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e) ∈ T := by
      have : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e) = (g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * k⁻¹ := by
        rw [hgk, mul_inv_cancel_right]
      rw [this]; exact T.mul_mem g.2 (T.inv_mem hkT)
    refine ⟨⟨k, hkT⟩, hk, ⟨toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e), hzT⟩, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]; intro u; exact Subtype.ext (toTensorGL_scalar_mul_comm (K := ℝ) (L := ℂ) e (u : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))).symm
    · exact Subtype.ext (by rw [hgk, toTensorGL_scalar_mul_comm (K := ℝ) (L := ℂ)]; rfl)
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_of_isInvInvariant τ'

  obtain ⟨U₁, hU₁, Ω, hΩ, hprop⟩ :=
    AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg c hc δ y hδ (tsupport φ) hφc

  obtain ⟨w, hwc, hws, hw0, hw1⟩ :=
    MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one τ' T.subtype hι Ω hΩ
  refine ⟨w, ⟨hw0, hwc.measurable, hws, fun x hx => ?_⟩, hwc⟩
  have hmem : x⁻¹ * ((1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * δ) * sigmaGL ℝ ℂ ℝ Complex.conjAe x ∈ tsupport φ := by
    rw [one_mul]; exact subset_tsupport _ hx
  obtain ⟨t, ht, d, hd, rfl⟩ := hprop 1 (mem_of_mem_nhds hU₁) T.one_mem x hmem
  have := hw1 ⟨t, ht⟩ d hd
  simpa [mul_assoc] using this

end Model

end Ws46.TsCent2

end

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace Ws46
namespace TsCent2Kit

section General

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L)

local notation "G" => GL (Fin 2) (L ⊗[K] A)

scoped instance instTopRing : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
scoped instance instTopGroup : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem isTwistedSectionFnOn_of_ne_zero_imp [TopologicalSpace A] (δ : G)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ ψ : G → ℂ) (hφψ : ∀ y, φ y ≠ 0 → ψ y ≠ 0) (w : G → ℝ)
    (hw : IsTwistedSectionFnOn K L A σ δ τ' ψ w) : IsTwistedSectionFnOn K L A σ δ τ' φ w :=
  ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x (hφψ _ hx)⟩

theorem exists_continuous_bump [T2Space A] [LocallyCompactSpace A] (φ : G → ℂ) (hφ : HasCompactSupport φ) :
    ∃ ψ : G → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ ∀ y, φ y ≠ 0 → ψ y ≠ 0 := by
  haveI : T2Space (GL (Fin 2) (L ⊗[K] A)) := t2Space_tensorGL K L A
  haveI : LocallyCompactSpace (GL (Fin 2) (L ⊗[K] A)) := locallyCompactSpace_tensorGL K L A
  obtain ⟨f, hf1, -, hfc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hφ.isCompact isClosed_empty (Set.disjoint_empty _)
  refine ⟨fun y => ((f y : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous, ?_, fun y hy => ?_⟩
  · exact hfc.comp_left Complex.ofReal_zero
  · have : f y = 1 := hf1 (subset_tsupport _ hy)
    simp [this]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem mem_twistedCentralizer_conj {δ y t : G} (ht : t ∈ twistedCentralizer K L A σ δ) :
    y⁻¹ * t * y ∈ twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  rw [map_mul, map_mul, map_inv]
  calc y⁻¹ * t * y * (y⁻¹ * δ * sigmaGL K L A σ y) * ((sigmaGL K L A σ y)⁻¹ * sigmaGL K L A σ t * sigmaGL K L A σ y)⁻¹
      = y⁻¹ * (t * δ * (sigmaGL K L A σ t)⁻¹) * sigmaGL K L A σ y := by group
    _ = y⁻¹ * δ * sigmaGL K L A σ y := by rw [ht]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem mem_twistedCentralizer_conj_iff (δ y t : G) :
    t ∈ twistedCentralizer K L A σ δ ↔
      y⁻¹ * t * y ∈ twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) := by
  refine ⟨mem_twistedCentralizer_conj σ, fun h => ?_⟩
  have h' := mem_twistedCentralizer_conj σ (y := y⁻¹) h
  have e1 : y⁻¹⁻¹ * (y⁻¹ * t * y) * y⁻¹ = t := by group
  have e2 : y⁻¹⁻¹ * (y⁻¹ * δ * sigmaGL K L A σ y) * sigmaGL K L A σ y⁻¹ = δ := by
    rw [map_inv]; group
  rwa [e1, e2] at h'

theorem exists_transport_conj [T2Space A] [LocallyCompactSpace A] (δ y : G)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ'' : @Measure (twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y))
        (twistedCentralizerBorel K L A σ (y⁻¹ * δ * sigmaGL K L A σ y)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ (y⁻¹ * δ * sigmaGL K L A σ y)) τ'' ∧
      ∀ (φ : G → ℂ) (w : G → ℝ),
        IsTwistedSectionFnOn K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) τ'' φ w →
        IsTwistedSectionFnOn K L A σ δ τ' φ (fun x => w (y⁻¹ * x)) ∧
          (Continuous w → Continuous (fun x => w (y⁻¹ * x))) := by
  set δ' : G := y⁻¹ * δ * sigmaGL K L A σ y with hδ'
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  letI : MeasurableSpace (twistedCentralizer K L A σ δ') := twistedCentralizerBorel K L A σ δ'
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ') := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  haveI : Measure.IsHaarMeasure τ' := hτ'

  let cFun : twistedCentralizer K L A σ δ → twistedCentralizer K L A σ δ' :=
    fun t => ⟨y⁻¹ * t * y, mem_twistedCentralizer_conj σ t.2⟩
  let cInv : twistedCentralizer K L A σ δ' → twistedCentralizer K L A σ δ :=
    fun s => ⟨y * s * y⁻¹, by
      have h := s.2
      rw [(mem_twistedCentralizer_conj_iff σ δ y (y * (s : G) * y⁻¹))]
      have : y⁻¹ * (y * (s : G) * y⁻¹) * y = s := by group
      rw [this]; exact h⟩
  let c : twistedCentralizer K L A σ δ ≃ₜ* twistedCentralizer K L A σ δ' :=
    { toFun := cFun
      invFun := cInv
      left_inv := fun t => Subtype.ext (by show y * (y⁻¹ * (t : G) * y) * y⁻¹ = t; group)
      right_inv := fun s => Subtype.ext (by show y⁻¹ * (y * (s : G) * y⁻¹) * y = s; group)
      map_mul' := fun s t => Subtype.ext (by
        show y⁻¹ * ((s : G) * t) * y = (y⁻¹ * s * y) * (y⁻¹ * t * y); group)
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_const.mul continuous_subtype_val).mul continuous_const
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_const.mul continuous_subtype_val).mul continuous_const }
  have hc_meas : Measurable c := c.continuous.measurable
  refine ⟨Measure.map c τ', ContinuousMulEquiv.isHaarMeasure_map τ' c, fun φ w hw => ⟨?_, fun hwc => ?_⟩⟩
  · refine ⟨fun x => hw.1 _, hw.2.1.comp (measurable_const_mul _), ?_, fun x hx => ?_⟩
    · exact hw.2.2.1.comp_homeomorph (Homeomorph.mulLeft y⁻¹)
    · have hx' : φ ((y⁻¹ * x)⁻¹ * δ' * sigmaGL K L A σ (y⁻¹ * x)) ≠ 0 := by
        have : (y⁻¹ * x)⁻¹ * δ' * sigmaGL K L A σ (y⁻¹ * x) = x⁻¹ * δ * sigmaGL K L A σ x := by
          rw [hδ', map_mul, map_inv]; group
        rwa [this]
      have key := hw.2.2.2 (y⁻¹ * x) hx'
      rw [MeasureTheory.integral_map hc_meas.aemeasurable] at key
      · convert key using 2
        funext t
        show w (y⁻¹ * ((t : G) * x)) = w (y⁻¹ * (t : G) * y * (y⁻¹ * x))
        congr 1; group
      · exact (hw.2.1.comp ((continuous_subtype_val.mul continuous_const).measurable)).aestronglyMeasurable
  · exact hwc.comp (continuous_const.mul continuous_id)

end General

section Iso

variable {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
  {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
  [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
  (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
  (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))

abbrev Ehat (E : L ⊗[K] A ≃+* L' ⊗[K'] A') : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L' ⊗[K'] A') :=
  Matrix.GeneralLinearGroup.map E.toRingHom

abbrev EhatInv (E : L ⊗[K] A ≃+* L' ⊗[K'] A') : GL (Fin 2) (L' ⊗[K'] A') →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map E.symm.toRingHom

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K' L']
  [TopologicalSpace A'] [IsTopologicalRing A'] in
theorem EhatInv_Ehat (x : GL (Fin 2) (L ⊗[K] A)) : EhatInv E (Ehat E x) = x := by
  apply Units.ext; ext i j
  show E.symm (E ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j)) = _
  exact E.symm_apply_apply _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K' L']
  [TopologicalSpace A'] [IsTopologicalRing A'] in
theorem Ehat_EhatInv (x : GL (Fin 2) (L' ⊗[K'] A')) : Ehat E (EhatInv E x) = x := by
  apply Units.ext; ext i j
  show E (E.symm ((x : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) i j)) = _
  exact E.apply_symm_apply _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K' L']
  [TopologicalSpace A'] [IsTopologicalRing A'] in
include hEσ in
theorem Ehat_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    Ehat E (sigmaGL K L A σ x) = sigmaGL K' L' A' σ' (Ehat E x) := by
  apply Units.ext; ext i j
  exact hEσ _

include hE in
theorem continuous_Ehat : Continuous (Ehat E : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) (L' ⊗[K'] A')) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => M.map E
  exact continuous_id.matrix_map hE

include hE' in
theorem continuous_EhatInv : Continuous (EhatInv E : GL (Fin 2) (L' ⊗[K'] A') → GL (Fin 2) (L ⊗[K] A)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A') => M.map E.symm
  exact continuous_id.matrix_map hE'

def EhatHomeo (hE : Continuous E) (hE' : Continuous E.symm) :
    GL (Fin 2) (L ⊗[K] A) ≃ₜ GL (Fin 2) (L' ⊗[K'] A') where
  toFun := Ehat E
  invFun := EhatInv E
  left_inv := EhatInv_Ehat E
  right_inv := Ehat_EhatInv E
  continuous_toFun := continuous_Ehat E hE
  continuous_invFun := continuous_EhatInv E hE'

include hE hE' hEσ in

theorem exists_transport_iso (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ'' : @Measure (twistedCentralizer K' L' A' σ' (Ehat E δ)) (twistedCentralizerBorel K' L' A' σ' (Ehat E δ)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K' L' A' σ' (Ehat E δ)) τ'' ∧
      ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L' ⊗[K'] A') → ℝ),
        IsTwistedSectionFnOn K' L' A' σ' (Ehat E δ) τ'' (φ ∘ EhatInv E) w →
        IsTwistedSectionFnOn K L A σ δ τ' φ (w ∘ Ehat E) ∧
          (Continuous w → Continuous (w ∘ Ehat E)) := by
  haveI : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
  haveI : IsTopologicalRing (L' ⊗[K'] A') := isTopologicalRing_tensor K' L' A'
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A
  haveI : IsTopologicalGroup (GL (Fin 2) (L' ⊗[K'] A')) := isTopologicalGroup_tensorGL K' L' A'
  set δ' := Ehat E δ with hδ'
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  letI : MeasurableSpace (twistedCentralizer K' L' A' σ' δ') := twistedCentralizerBorel K' L' A' σ' δ'
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K' L' A' σ' δ') := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  letI : MeasurableSpace (GL (Fin 2) (L' ⊗[K'] A')) := glBorelOf (L' ⊗[K'] A')
  haveI : BorelSpace (GL (Fin 2) (L' ⊗[K'] A')) := borelSpace_glBorelOf _
  haveI : Measure.IsHaarMeasure τ' := hτ'
  have hmem : ∀ t : GL (Fin 2) (L ⊗[K] A), t ∈ twistedCentralizer K L A σ δ →
      Ehat E t ∈ twistedCentralizer K' L' A' σ' δ' := by
    intro t ht
    rw [mem_sigmaCentralizer_iff] at ht ⊢
    rw [hδ', ← Ehat_sigmaGL σ σ' E hEσ, ← map_inv, ← map_mul, ← map_mul, ht]
  have hmem' : ∀ s : GL (Fin 2) (L' ⊗[K'] A'), s ∈ twistedCentralizer K' L' A' σ' δ' →
      EhatInv E s ∈ twistedCentralizer K L A σ δ := by
    intro s hs
    rw [mem_sigmaCentralizer_iff] at hs ⊢
    have h1 : Ehat E (EhatInv E s * δ * (sigmaGL K L A σ (EhatInv E s))⁻¹) = δ' := by
      rw [map_mul, map_mul, map_inv, Ehat_sigmaGL σ σ' E hEσ, Ehat_EhatInv, ← hδ', hs]
    have h2 := congrArg (EhatInv E) h1
    rwa [EhatInv_Ehat, hδ', EhatInv_Ehat] at h2
  let c : twistedCentralizer K L A σ δ ≃ₜ* twistedCentralizer K' L' A' σ' δ' :=
    { toFun := fun t => ⟨Ehat E t, hmem t t.2⟩
      invFun := fun s => ⟨EhatInv E s, hmem' s s.2⟩
      left_inv := fun t => Subtype.ext (EhatInv_Ehat E t)
      right_inv := fun s => Subtype.ext (Ehat_EhatInv E s)
      map_mul' := fun s t => Subtype.ext
        (map_mul (Ehat E) (s : GL (Fin 2) (L ⊗[K] A)) (t : GL (Fin 2) (L ⊗[K] A)))
      continuous_toFun := Continuous.subtype_mk ((continuous_Ehat E hE).comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk ((continuous_EhatInv E hE').comp continuous_subtype_val) _ }
  have hc_meas : Measurable c := c.continuous.measurable
  refine ⟨Measure.map c τ', ContinuousMulEquiv.isHaarMeasure_map τ' c, fun φ w hw => ⟨?_, fun hwc => ?_⟩⟩
  · refine ⟨fun x => hw.1 _, hw.2.1.comp (continuous_Ehat E hE).measurable, ?_, fun x hx => ?_⟩
    · exact hw.2.2.1.comp_homeomorph (EhatHomeo E hE hE')
    · have hx' : (φ ∘ EhatInv E) ((Ehat E x)⁻¹ * δ' * sigmaGL K' L' A' σ' (Ehat E x)) ≠ 0 := by
        have : (Ehat E x)⁻¹ * δ' * sigmaGL K' L' A' σ' (Ehat E x) = Ehat E (x⁻¹ * δ * sigmaGL K L A σ x) := by
          rw [map_mul, map_mul, map_inv, Ehat_sigmaGL σ σ' E hEσ]
        rw [this, Function.comp_apply, EhatInv_Ehat]
        exact hx
      have key := hw.2.2.2 (Ehat E x) hx'
      rw [MeasureTheory.integral_map hc_meas.aemeasurable] at key
      · convert key using 2
        funext t
        show w (Ehat E ((t : GL (Fin 2) (L ⊗[K] A)) * x)) = w (Ehat E t * Ehat E x)
        rw [map_mul]
      · exact (hw.2.1.comp ((continuous_subtype_val.mul continuous_const).measurable)).aestronglyMeasurable
  · exact hwc.comp (continuous_Ehat E hE)

end Iso

section NormString

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] in
theorem sigmaTensor_tmul' (l : L) (a : A) : sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sigmaTensor]

omit [FiniteDimensional K L] in

theorem exists_eq_tmul_of_fixed (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (u : L ⊗[K] A) (hu : sigmaTensor K L A σ u = u) : ∃ a : A, u = (1 : L) ⊗ₜ[K] a := by
  have hex : Function.Exact (Algebra.linearMap K L) (σ.toLinearMap - LinearMap.id : L →ₗ[K] L) := by
    intro l
    constructor
    · intro hl
      have : σ l - l = 0 := hl
      exact hfix l (sub_eq_zero.1 this)
    · rintro ⟨k, rfl⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Algebra.linearMap_apply,
        AlgEquiv.toLinearMap_apply, AlgEquiv.commutes, sub_self]
  have hexA := Module.Flat.rTensor_exact A hex
  have hrT : ∀ w : L ⊗[K] A, ((σ.toLinearMap - LinearMap.id).rTensor A) w = sigmaTensor K L A σ w - w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
        rw [LinearMap.rTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply, TensorProduct.sub_tmul,
          sigmaTensor_tmul']
        rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]; abel
  have hu0 : ((σ.toLinearMap - LinearMap.id).rTensor A) u = 0 := by rw [hrT, hu, sub_self]
  obtain ⟨w, hw⟩ := (hexA u).1 hu0
  rw [← hw]
  clear hw hu0 hu
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul k a =>
      refine ⟨k • a, ?_⟩
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩

omit [FiniteDimensional K L] in
private theorem _root_.Ws46.TsCent2Kit.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "Ws46.TsCent2Kit" "includeRight_injective"

theorem iterate_sigmaTensor_finrank [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L ⊗[K] A) : (⇑(sigmaTensor K L A σ))^[Module.finrank K L] x = x := by
  rw [← RingHom.coe_pow]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      have : ∀ n : ℕ, ((sigmaTensor K L A σ) ^ n) (l ⊗ₜ a) = ((⇑σ)^[n] l) ⊗ₜ a := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, sigmaTensor_tmul',
              Function.iterate_succ_apply']
      rw [this, LT.TwistedNorm.iterate_finrank_apply_of_generator hgen]
  | add x y hx hy => rw [map_add, hx, hy]

theorem iterate_sigmaGL_finrank [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  apply Units.ext; ext i j
  rw [show sigmaGL K L A σ = Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ) from rfl,
    LT.TwistedNorm.iterate_generalLinearGroup_map_apply]
  exact iterate_sigmaTensor_finrank σ hgen _

omit [FiniteDimensional K L] in
theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  rfl

omit [FiniteDimensional K L] in
theorem sigmaGL_scalar (u : (L ⊗[K] A)ˣ) :
    sigmaGL K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigmaTensor K L A σ).toMonoidHom u) := by
  apply Units.ext; ext i j
  show sigmaTensor K L A σ ((Matrix.scalar (Fin 2) (u : L ⊗[K] A)) i j) = (Matrix.scalar (Fin 2) _) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

omit [FiniteDimensional K L] in
theorem scalar_mul_comm' (c : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : L ⊗[K] A) * (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * Matrix.scalar (Fin 2) (c : L ⊗[K] A)
  exact (Matrix.scalar_commute (c : L ⊗[K] A) (fun r => Commute.all _ r) _).eq

omit [FiniteDimensional K L] in
theorem scalar_includeRight (z : Aˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom z) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  apply Units.ext; ext i j
  show (Matrix.scalar (Fin 2) _) i j =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((Matrix.scalar (Fin 2) (z : A)) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact (map_zero _).symm

theorem exists_normString_eq_toTensorGL_scalar [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : ∃ d : (L ⊗[K] A)ˣ, IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) :
    ∃ z : Aˣ, normString K L A σ δ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  obtain ⟨d, y, hy⟩ := hδ
  set n := Module.finrank K L with hn
  set σG := sigmaGL K L A σ with hσG
  set σU : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ := Units.map (sigmaTensor K L A σ).toMonoidHom with hσU

  have hfixG : ∀ g : GL (Fin 2) (L ⊗[K] A), (⇑σG)^[n] g = g := iterate_sigmaGL_finrank σ hgen
  have h1 : LT.TwistedNorm.sigmaNormPow σG n (Matrix.GeneralLinearGroup.scalar (Fin 2) d) =
      y⁻¹ * LT.TwistedNorm.sigmaNormPow σG n δ * y := by
    rw [hy, LT.TwistedNorm.sigmaNormPow_sigmaConjElt σG n (hfixG y)]
  have h2 : LT.TwistedNorm.sigmaNormPow σG n (Matrix.GeneralLinearGroup.scalar (Fin 2) d) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (LT.TwistedNorm.sigmaNormPow σU n d) := by
    have := LT.TwistedNorm.hom_sigmaNormPow σU σG (Matrix.GeneralLinearGroup.scalar (Fin 2))
      (fun x => (sigmaGL_scalar σ x).symm) n d
    exact this.symm
  set Nd := LT.TwistedNorm.sigmaNormPow σU n d with hNd

  have hfixU : ∀ u : (L ⊗[K] A)ˣ, (⇑σU)^[n] u = u := by
    intro u; apply Units.ext
    have : ∀ m : ℕ, (((⇑σU)^[m] u : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑(sigmaTensor K L A σ))^[m] (u : L ⊗[K] A) := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
    rw [this]; exact iterate_sigmaTensor_finrank σ hgen _
  have hNdfix : sigmaTensor K L A σ (Nd : L ⊗[K] A) = Nd := by
    have h := congrArg Units.val (LT.TwistedNorm.map_sigmaNormPow σU n (hfixU d))
    rw [Units.val_mul, Units.val_mul] at h
    have e : ((d⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (Nd : L ⊗[K] A) * (d : L ⊗[K] A) = Nd := by
      rw [show ((d⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (Nd : L ⊗[K] A) * (d : L ⊗[K] A) =
        (Nd : L ⊗[K] A) * (((d⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * d) by ring, Units.inv_mul, mul_one]
    rw [← hNd, e] at h
    exact h
  have hσUNd : σU Nd = Nd := Units.ext hNdfix
  have hNdfix' : sigmaTensor K L A σ ((Nd⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (Nd⁻¹ : (L ⊗[K] A)ˣ) := by
    show ((σU Nd⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = _
    rw [map_inv, hσUNd]
  have hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L) := fun l hl =>
    LT.TwistedNorm.mem_range_algebraMap_of_generator_apply_eq hgen hl
  obtain ⟨a, ha⟩ := exists_eq_tmul_of_fixed σ hfix _ hNdfix
  obtain ⟨b, hb⟩ := exists_eq_tmul_of_fixed σ hfix _ hNdfix'
  have hab : a * b = 1 := by
    apply includeRight_injective (K := K) (L := L) (A := A)
    rw [map_mul, map_one]
    show ((1 : L) ⊗ₜ[K] a) * ((1 : L) ⊗ₜ[K] b) = 1
    rw [← ha, ← hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let z : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨z, ?_⟩
  have hNdz : Nd = Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom z :=
    Units.ext ha
  calc normString K L A σ δ = LT.TwistedNorm.sigmaNormPow σG n δ := normString_eq_sigmaNormPow σ δ
    _ = y * (y⁻¹ * LT.TwistedNorm.sigmaNormPow σG n δ * y) * y⁻¹ := by group
    _ = y * Matrix.GeneralLinearGroup.scalar (Fin 2) Nd * y⁻¹ := by rw [← h1, h2]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 2) Nd := by rw [← scalar_mul_comm', mul_inv_cancel_right]
    _ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by rw [hNdz, scalar_includeRight]

end NormString

section Model

def eRing : (ℂ ⊗[ℝ] ℝ) ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem eRing_tmul (z : ℂ) (a : ℝ) : eRing (z ⊗ₜ[ℝ] a) = (a : ℂ) * z := by
  show (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ[ℝ] a) = (a : ℂ) * z
  rw [Algebra.TensorProduct.rid_tmul, Complex.real_smul]

theorem eRing_sigmaTensor (x : ℂ ⊗[ℝ] ℝ) :
    eRing (sigmaTensor ℝ ℂ ℝ Complex.conjAe x) = (starRingEnd ℂ) (eRing x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a =>
      rw [sigmaTensor_tmul', eRing_tmul, eRing_tmul, map_mul, Complex.conj_ofReal]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add eRing x y, map_add]

theorem exists_conj_eq_mul_of_norm_eq_one (ω : ℂ) (hω : ‖ω‖ = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ (starRingEnd ℂ) c = ω * c := by
  by_cases h : ω = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    rw [h, Complex.conj_I, neg_one_mul]
  · refine ⟨1 + (starRingEnd ℂ) ω, ?_, ?_⟩
    · intro h0
      apply h
      have : (starRingEnd ℂ) ω = -1 := by linear_combination h0
      have := congrArg (starRingEnd ℂ) this
      rwa [Complex.conj_conj, map_neg, map_one] at this
    · have hωω : ω * (starRingEnd ℂ) ω = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; norm_num
      rw [map_add, map_one, Complex.conj_conj, mul_add, mul_one, hωω, add_comm]

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom u) := by
  apply Units.ext; ext i j
  show f ((Matrix.scalar (Fin 2) (u : R)) i j) = (Matrix.scalar (Fin 2) _) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem exists_toTensorGL_real_scalar_eq (d' : (ℂ ⊗[ℝ] ℝ)ˣ) :
    ∃ (d₀ : ℝˣ) (c : (ℂ ⊗[ℝ] ℝ)ˣ),
      toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d₀) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) d' *
          sigmaGL ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  set u : ℂ := eRing (d' : ℂ ⊗[ℝ] ℝ) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact (d'.isUnit.map eRing.toRingHom.toMonoidHom).ne_zero
  set r : ℝ := ‖u‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hu0
  set ω : ℂ := (r : ℂ) / u with hω
  have hω1 : ‖ω‖ = 1 := by
    rw [hω, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hr, div_self (norm_ne_zero_iff.2 hu0)]
  obtain ⟨cC, hc0, hc⟩ := exists_conj_eq_mul_of_norm_eq_one ω hω1

  have key : cC⁻¹ * u * (starRingEnd ℂ) cC = r := by
    rw [hc, hω]; field_simp
  let d₀ : ℝˣ := Units.mk0 r hr0.ne'
  let c : (ℂ ⊗[ℝ] ℝ)ˣ := Units.map eRing.symm.toRingHom.toMonoidHom (Units.mk0 cC hc0)
  refine ⟨d₀, c, ?_⟩
  rw [← scalar_includeRight, sigmaGL_scalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  apply eRing.injective
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  show eRing ((1 : ℂ) ⊗ₜ[ℝ] (r : ℝ)) =
    eRing (eRing.symm (cC⁻¹)) * u * eRing (sigmaTensor ℝ ℂ ℝ Complex.conjAe (eRing.symm cC))
  rw [eRing_tmul, mul_one, eRing_sigmaTensor, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, key]

end Model

section Assembly

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L)

theorem exists_transport_conj' [T2Space A] [LocallyCompactSpace A] (δ y δ' : GL (Fin 2) (L ⊗[K] A))
    (hδ' : δ' = y⁻¹ * δ * sigmaGL K L A σ y)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ'' : @Measure (twistedCentralizer K L A σ δ') (twistedCentralizerBorel K L A σ δ'),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ') τ'' ∧
      ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L ⊗[K] A) → ℝ),
        IsTwistedSectionFnOn K L A σ δ' τ'' φ w →
        IsTwistedSectionFnOn K L A σ δ τ' φ (fun x => w (y⁻¹ * x)) ∧
          (Continuous w → Continuous (fun x => w (y⁻¹ * x))) := by
  subst hδ'
  exact exists_transport_conj σ δ y τ' hτ'

end Assembly

section Main

open NumberField

theorem sigma_ne_one {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : σ ≠ 1 := by
  intro h
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hsub : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen τ)
    rw [← hk, h, one_zpow]
  have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hsub a).trans (hsub b).symm⟩, ⟨1⟩⟩
  rw [h1] at hcard
  exact hprime.one_lt.ne hcard

end Main

end Ws46.TsCent2Kit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"

noncomputable section

namespace Ws46
namespace TsCent2

open Ws46.TsCent2Kit NumberField

section NormTransport

variable {K L A : Type} [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)
  {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L']
  [CommRing A'] [Algebra K' A'] (σ' : L' ≃ₐ[K'] L')

theorem map_normString' (h : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L' ⊗[K'] A'))
    (hσ : ∀ g, h (sigmaGL K L A σ g) = sigmaGL K' L' A' σ' (h g))
    (hrank : Module.finrank K L = Module.finrank K' L') (δ : GL (Fin 2) (L ⊗[K] A)) :
    h (normString K L A σ δ) = normString K' L' A' σ' (h δ) := by
  unfold normString
  rw [map_list_prod, List.map_map, hrank]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  have hs : Function.Semiconj (⇑h) (⇑(sigmaGL K L A σ)) (⇑(sigmaGL K' L' A' σ')) := hσ
  exact (hs.iterate_right i) δ

end NormTransport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"

section Main2

set_option maxHeartbeats 16000000 in

theorem main2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (c : (v.Completion)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (hδq : ∀ z : (L ⊗[K] v.Completion)ˣ,
      ¬ IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [h2]; exact two_pos)
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  have hprime : (Module.finrank K L).Prime := by rw [h2]; exact Nat.prime_two
  have hσ1 : σ ≠ 1 := sigma_ne_one hprime σ hgen

  obtain ⟨w, rfl⟩ := NumberField.InfinitePlace.comap_surjective (k := K) (K := L) v
  by_cases hun : w.IsUnramified K
  ·
    obtain ⟨ι⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L
      (w.comap (algebraMap K L)) w rfl hun
    obtain ⟨z, hz⟩ :=
      AutomorphicForm.exists_isSigmaConjugate_scalar_of_isNormConjugator_scalar_of_algHom_of_prime
        K L hprime σ hσ1 _ ι c δ y hδ
    exact absurd hz (hδq z)
  ·
    obtain ⟨e, E, he, he', hE, hE', hEσ, hEι, hErid, heK⟩ :=
      AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified K L h2 σ hσ1 w hun
    obtain ⟨τ₂, hτ₂, htr₂⟩ := exists_transport_iso σ Complex.conjAe E hE hE' hEσ δ τ' hτ'

    set c' : ℝˣ := Units.map e.toRingHom.toMonoidHom c with hc'
    have hEσ' : ∀ g, Ehat E (sigmaGL K L _ σ g) = sigmaGL ℝ ℂ ℝ Complex.conjAe (Ehat E g) :=
      fun g => Ehat_sigmaGL σ Complex.conjAe E hEσ g
    have hrank : Module.finrank K L = Module.finrank ℝ ℂ := by rw [h2, Complex.finrank_real_complex]
    have hδ' : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c') (Ehat E δ) (Ehat E y) := by
      unfold IsNormConjugator at hδ ⊢
      have h1 := congrArg (Ehat E) hδ
      rw [map_mul, map_mul, map_inv, map_normString' σ Complex.conjAe (Ehat E) hEσ' hrank] at h1
      rw [← h1, hc', ← map_scalar, ← hEι]

    have hq' : ¬ ∃ z : (ℂ ⊗[ℝ] ℝ)ˣ, IsSigmaConjugate ℝ ℂ ℝ Complex.conjAe (Ehat E δ) (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
      rintro ⟨z, x, hx⟩
      apply hδq (Units.map E.symm.toRingHom.toMonoidHom z)
      refine ⟨EhatInv E x, ?_⟩
      have h1 := congrArg (EhatInv E) hx
      rw [map_mul, map_mul, map_inv, EhatInv_Ehat] at h1
      have hσi : EhatInv E (sigmaGL ℝ ℂ ℝ Complex.conjAe x) = sigmaGL K L _ σ (EhatInv E x) := by
        have := (hEσ' (EhatInv E x)).symm
        rw [Ehat_EhatInv] at this
        rw [this, EhatInv_Ehat]
      rw [hσi] at h1
      rw [← h1]
      exact (map_scalar E.symm.toRingHom z).symm
    have hc'neg : (c' : ℝ) < 0 := by
      have hiff := AutomorphicForm.exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
        c' (Ehat E δ) (Ehat E y) hδ'
      have hle : ¬ (0 < (c' : ℝ)) := fun h => hq' (hiff.2 h)
      exact lt_of_le_of_ne (not_lt.1 hle) c'.ne_zero

    have hφ' : HasCompactSupport (φ ∘ EhatInv E) := hφc.comp_homeomorph (EhatHomeo E hE hE').symm
    obtain ⟨w₀, hw₀, hw₀c⟩ :=
      exists_isTwistedSectionFnOn_conjAe_of_neg c' hc'neg (Ehat E δ) (Ehat E y) hδ' τ₂ hτ₂ (φ ∘ EhatInv E) hφ'
    obtain ⟨hw, hwc⟩ := htr₂ φ w₀ hw₀
    exact ⟨_, hw, hwc hw₀c⟩

end Main2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"

end Ws46.TsCent2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46 P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.Ws46.TsCent2Kit"

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (c : (v.Completion)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (hδq : ∀ z : (L ⊗[K] v.Completion)ˣ,
      ¬ IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W :=
  Ws46.TsCent2.main2 K L h2 σ hgen v c δ y hδ hδq τ' hτ' φ hφ hφc

end S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
