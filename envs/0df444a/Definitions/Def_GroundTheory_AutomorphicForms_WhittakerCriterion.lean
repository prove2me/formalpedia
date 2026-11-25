-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- name    : GroundTheory_AutomorphicForms_WhittakerCriterion
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:56.609883+00:00
-- url     : https://prove2.me/theorems/1d134fbc-c662-4d3f-aa16-f869d26fcc19
-- title:
--   Whittaker Criterion
-- statement:
--   Definitions and structural lemmas for Whittaker Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_right
import Theorems.Thm_GroundTheory_Automorphic_indicator_mem_locallyConstantCompactSupport
import Theorems.Thm_GroundTheory_Automorphic_mem_locallyConstantCompactSupport

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
namespace Whittaker
open Set Filter Topology MeasureTheory
section Translations
variable {X : Type*} [TopologicalSpace X]
def compHomeoL (e : X ≃ₜ X) :
    locallyConstantCompactSupport X ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport X ℂ ℂ where
  toFun f := ⟨(f : X → ℂ) ∘ e, mem_locallyConstantCompactSupport.2
    ⟨f.2.1.comp_continuous e.continuous, f.2.2.comp_homeomorph e⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp]
theorem coe_compHomeoL (e : X ≃ₜ X) (f : locallyConstantCompactSupport X ℂ ℂ) :
    ((compHomeoL e f : locallyConstantCompactSupport X ℂ ℂ) : X → ℂ) = (f : X → ℂ) ∘ e := rfl
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def biTranslL (a b : G) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport G ℂ ℂ :=
  compHomeoL ((Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight b))
@[simp]
theorem coe_biTranslL (a b : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ((biTranslL a b f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) =
      fun x => (f : G → ℂ) (a⁻¹ * x * b) := rfl
def rtransL (g : G) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport G ℂ ℂ :=
  compHomeoL (Homeomorph.mulRight g)
@[simp]
theorem coe_rtransL (g : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ((rtransL g f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) = fun x => (f : G → ℂ) (x * g) :=
  rfl
def ltransL (a : G) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] locallyConstantCompactSupport G ℂ ℂ :=
  compHomeoL (Homeomorph.mulLeft a⁻¹)
@[simp]
theorem coe_ltransL (a : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ((ltransL a f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) = fun x => (f : G → ℂ) (a⁻¹ * x) :=
  rfl
end Translations
section Distributions
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def BiEquivariantSigmaInvariant (H : Subgroup G) (χ : H → ℂ) (σ : G ≃ₜ G) : Prop :=
  ∀ D : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ),
    (∀ (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H),
      D (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * D f) →
    ∀ f, D (compHomeoL σ f) = D f
end Distributions
section Hecke
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem heckeAct_apply_act [μ.IsMulRightInvariant] {f : G → ℂ} (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V}
    (hv : v ∈ smoothVectors ρ) (g : G) :
    heckeAct μ ρ f (ρ g v) = heckeAct μ ρ (fun x => f (x * g⁻¹)) v := by
  have hf' : (fun x => f (x * g⁻¹)) ∈ locallyConstantCompactSupport G ℂ ℂ :=
    (rtransL g⁻¹ ⟨f, hf⟩).2
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ hf (smooth_apply_mem ρ hv g), dual_heckeAct μ hf' hv,
    ← integral_mul_right_eq_self (fun x => f (x * g⁻¹) * φ (ρ x v)) g]
  simp only [mul_inv_cancel_right, map_mul, Module.End.mul_apply]
def normInd (K : Subgroup G) : G → ℂ :=
  (K : Set G).indicator fun _ => ((μ.real (K : Set G))⁻¹ : ℂ)
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [BorelSpace G] [μ.IsHaarMeasure] in
theorem normInd_mem {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    normInd μ K ∈ locallyConstantCompactSupport G ℂ ℂ :=
  indicator_mem_locallyConstantCompactSupport hKc hKo _
variable (hρ : IsSmooth ρ)
include hρ
def heckeLin (f : locallyConstantCompactSupport G ℂ ℂ) : V →ₗ[ℂ] V where
  toFun v := heckeAct μ ρ f v
  map_add' v w := heckeAct_add_right f.2 (hρ v) (hρ w)
  map_smul' c v := heckeAct_smul_right f.2 c (hρ v)
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
@[simp]
theorem heckeLin_apply (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    heckeLin μ hρ f v = heckeAct μ ρ f v := rfl
theorem comp_heckeLin_mem [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) :
    ℓ ∘ₗ heckeLin μ hρ f ∈ smoothVectors (Representation.dual ρ) := by
  obtain ⟨K, -, hK⟩ := exists_forall_mul_right f.2
  refine mem_smoothVectors_of_mem_fixedVectors (H := (K : Subgroup G)) K.isOpen
    (mem_fixedVectors_dual.2 fun k hk v => ?_)
  simp only [LinearMap.comp_apply, heckeLin_apply]
  rw [heckeAct_apply_act μ f.2 (hρ v) k]
  congr 2
  funext x
  exact hK x k⁻¹ (inv_mem hk)
def coeffL [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) :
    locallyConstantCompactSupport G ℂ ℂ →ₗ[ℂ] smoothVectors (Representation.dual ρ) where
  toFun f := ⟨ℓ ∘ₗ heckeLin μ hρ f, comp_heckeLin_mem μ hρ ℓ f⟩
  map_add' f g := Subtype.ext <| LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, heckeLin_apply, Submodule.coe_add, LinearMap.add_apply]
    rw [heckeAct_add_left f.2 g.2 (hρ v), map_add]
  map_smul' c f := Subtype.ext <| LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, heckeLin_apply, SetLike.val_smul, LinearMap.smul_apply,
      RingHom.id_apply]
    rw [heckeAct_smul_left c f.2 (hρ v), map_smul]
def convS (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) : locallyConstantCompactSupport G ℂ ℂ :=
  ⟨groupConv μ f₁ f₂, groupConv_mem μ f₁.2 f₂.2⟩
end Hecke
section Equivariant
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
def equivariantFunctionals (ρ : Representation ℂ G V) {H : Subgroup G} (χ : H → ℂ) :
    Submodule ℂ (Module.Dual ℂ V) where
  carrier := {ℓ | ∀ h : H, ∀ v, ℓ (ρ h v) = χ h * ℓ v}
  add_mem' {a b} ha hb h v := by
    simp only [Set.mem_ofPred_eq, LinearMap.add_apply] at ha hb ⊢
    rw [ha h v, hb h v, mul_add]
  zero_mem' h v := by simp
  smul_mem' c ℓ hℓ h v := by
    simp only [Set.mem_ofPred_eq, LinearMap.smul_apply, smul_eq_mul] at hℓ ⊢
    rw [hℓ h v]
    ring
end Equivariant
section Sigma
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
end Sigma
section Distribution
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
def coeffDist (ℓ : Module.Dual ℂ V) (ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) :
    Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) :=
  ℓt ∘ₗ coeffL μ hρ ℓ
end Distribution
section Contragredient
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

def annihilatorSubrep (W : Subrepresentation (contragredient ρ)) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) v = 0}
      add_mem' := fun {a b} ha hb => by
        show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) (a + b) = 0
        intro ξ hξ
        rw [map_add, ha ξ hξ, hb ξ hξ, add_zero]
      zero_mem' := by
        show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) 0 = 0
        intro ξ _
        exact map_zero _
      smul_mem' := fun c v hv => by
        show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) (c • v) = 0
        intro ξ hξ
        rw [map_smul, hv ξ hξ, smul_zero] }
  apply_mem_toSubmodule g v hv := by
    show ∀ ξ ∈ W, (ξ : Module.Dual ℂ V) (ρ g v) = 0
    intro ξ hξ
    have := hv _ (W.apply_mem_toSubmodule g⁻¹ hξ)
    rwa [contragredient_apply_apply, inv_inv] at this
end Contragredient
section Surjective
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
end Surjective
section Criterion
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
def coeffKer (hρ : IsSmooth ρ) (ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) :
    Submodule ℂ (locallyConstantCompactSupport G ℂ ℂ) where
  carrier := {k | ∀ ξ : smoothVectors (Representation.dual ρ),
    ℓt (coeffL μ hρ (ξ : Module.Dual ℂ V) k) = 0}
  add_mem' {a b} ha hb ξ := by
    rw [map_add, map_add, ha ξ, hb ξ, add_zero]
  zero_mem' ξ := by rw [map_zero, map_zero]
  smul_mem' c k hk ξ := by
    rw [map_smul, map_smul, hk ξ, smul_zero]
variable [μ.IsInvInvariant] {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}
end Criterion
section Unimodular
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
end Unimodular
section Main
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace.SeparableSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}
end Main
end Whittaker
end GroundTheory.Automorphic


