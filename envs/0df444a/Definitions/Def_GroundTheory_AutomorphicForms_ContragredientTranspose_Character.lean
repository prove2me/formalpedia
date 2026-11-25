-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
-- name    : GroundTheory_AutomorphicForms_ContragredientTranspose_Character
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:49.74283+00:00
-- url     : https://prove2.me/theorems/eb09b888-6dcf-4d17-97b2-2af52bd9ca17
-- title:
--   Character
-- statement:
--   Definitions and structural lemmas for Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_coe_smul_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
section FinTrace
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def finTrace (T : V →ₗ[ℂ] V) : ℂ :=
  LinearMap.trace ℂ (LinearMap.range T) (T.restrict fun x _ => LinearMap.mem_range_self T x)
theorem finTrace_eq_trace (T : V →ₗ[ℂ] V) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (hE : LinearMap.range T ≤ E) :
    LinearMap.trace ℂ E (T.restrict fun x _ => hE (LinearMap.mem_range_self T x)) =
      finTrace T := by
  have : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hE
  let A : E →ₗ[ℂ] LinearMap.range T :=
    (T ∘ₗ E.subtype).codRestrict _ fun x => LinearMap.mem_range_self T x
  let B : LinearMap.range T →ₗ[ℂ] E := Submodule.inclusion hE
  have h1 : (T.restrict fun x _ => hE (LinearMap.mem_range_self T x) : E →ₗ[ℂ] E) = B ∘ₗ A :=
    LinearMap.ext fun x => Subtype.ext rfl
  have h2 : (T.restrict fun x _ => LinearMap.mem_range_self T x :
      LinearMap.range T →ₗ[ℂ] LinearMap.range T) = A ∘ₗ B :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [finTrace, h1, h2, LinearMap.trace_comp_comm']
theorem finTrace_add (S T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range S)]
    [FiniteDimensional ℂ (LinearMap.range T)] :
    finTrace (S + T) = finTrace S + finTrace T := by
  set E := LinearMap.range S ⊔ LinearMap.range T
  have hS : LinearMap.range S ≤ E := le_sup_left
  have hT : LinearMap.range T ≤ E := le_sup_right
  have hST : LinearMap.range (S + T) ≤ E := by
    rintro _ ⟨x, rfl⟩
    exact E.add_mem (hS ⟨x, rfl⟩) (hT ⟨x, rfl⟩)
  rw [← finTrace_eq_trace S E hS, ← finTrace_eq_trace T E hT, ← finTrace_eq_trace (S + T) E hST,
    ← map_add]
  congr 1
theorem finTrace_smul (c : ℂ) (T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range T)] :
    finTrace (c • T) = c * finTrace T := by
  have h : LinearMap.range (c • T) ≤ LinearMap.range T := by
    rintro _ ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩
  rw [← finTrace_eq_trace (c • T) (LinearMap.range T) h, finTrace, ← smul_eq_mul, ← map_smul]
  congr 1
end FinTrace
section Character
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem range_heckeLin_le (hρ : IsSmooth ρ) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hK : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    LinearMap.range (heckeLin μ hρ f) ≤ fixedVectors ρ K := by
  rintro _ ⟨v, rfl⟩
  exact heckeAct_mem_fixedVectors f.2 hK (hρ v)
theorem finiteDimensional_range_heckeLin (hρ : IsAdmissible ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    FiniteDimensional ℂ (LinearMap.range (heckeLin μ hρ.1 f)) := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left f.2
  have := hρ.2 K hKc K.isOpen
  exact Submodule.finiteDimensional_of_le (range_heckeLin_le μ hρ.1 f (K := K) hK)
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeLin_add (hρ : IsSmooth ρ) (f g : locallyConstantCompactSupport G ℂ ℂ) :
    heckeLin μ hρ (f + g) = heckeLin μ hρ f + heckeLin μ hρ g :=
  LinearMap.ext fun v => heckeAct_add_left f.2 g.2 (hρ v)
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeLin_smul (hρ : IsSmooth ρ) (c : ℂ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    heckeLin μ hρ (c • f) = c • heckeLin μ hρ f :=
  LinearMap.ext fun v => heckeAct_smul_left c f.2 (hρ v)
variable (ρ) in

def distChar (hρ : IsAdmissible ρ) : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) where
  toFun f := finTrace (heckeLin μ hρ.1 f)
  map_add' f g := by
    have := finiteDimensional_range_heckeLin μ hρ f
    have := finiteDimensional_range_heckeLin μ hρ g
    simp only [heckeLin_add]
    exact finTrace_add _ _
  map_smul' c f := by
    have := finiteDimensional_range_heckeLin μ hρ f
    simp only [heckeLin_smul, RingHom.id_apply, smul_eq_mul]
    exact finTrace_smul c _
variable (ρ) in

def repEquiv (g : G) : V ≃ₗ[ℂ] V where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv v := by
    change (ρ g⁻¹ * ρ g) v = v
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change (ρ g * ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
end Character
section Contragredient
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
def mulEquivHomeo (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm) : G ≃ₜ G where
  toEquiv := α.toEquiv
  continuous_toFun := hα
  continuous_invFun := hα'
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in

@[simp]
theorem mulEquivHomeo_apply (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm) (x : G) :
    mulEquivHomeo α hα hα' x = α x := rfl
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in

@[simp]
theorem mulEquivHomeo_symm_apply (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (x : G) : (mulEquivHomeo α hα hα').symm x = α.symm x := rfl
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in

theorem isAdmissible_comp (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hρ : IsAdmissible ρ) : IsAdmissible (ρ.comp α.toMonoidHom) := by
  refine ⟨fun v => (hρ.1 v).preimage hα, fun K hKc hKo => ?_⟩
  have e : fixedVectors (ρ.comp α.toMonoidHom) K = fixedVectors ρ (K.map α.toMonoidHom) := by
    ext v
    simp only [mem_fixedVectors, Subgroup.mem_map]
    constructor
    · rintro h _ ⟨k, hk, rfl⟩
      exact h k hk
    · intro h k hk
      exact h _ ⟨k, hk, rfl⟩
  rw [e]
  refine hρ.2 _ ?_ ?_
  · rw [Subgroup.coe_map]
    exact hKc.image hα
  · rw [Subgroup.coe_map]
    exact (mulEquivHomeo α hα hα').isOpenMap _ hKo
end Contragredient
section Independence
open HeckeAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
variable (ρ : Representation ℂ G V) in

def levelLin (h : HeckeAlgebraLevel μ K hKc hKo) : fixedVectors ρ K →ₗ[ℂ] fixedVectors ρ K where
  toFun v := h • v
  map_add' v w := smul_add h v w
  map_smul' c v := Subtype.ext (by
    simp only [RingHom.id_apply, HeckeAlgebraLevel.coe_smul_fixedVectors, Submodule.coe_smul]
    exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo v.2))
end Independence
end ContragredientTranspose
end GroundTheory.Automorphic


