-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
-- name    : GroundTheory_AutomorphicForms_SmoothRepContragredient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:44.726798+00:00
-- url     : https://prove2.me/theorems/f623ec1a-7149-46f9-a7f6-a08146a1e3fd
-- title:
--   Smooth Rep Contragredient
-- statement:
--   Definitions and structural lemmas for Smooth Rep Contragredient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_eq_of_invariant_of_eqOn
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors_iff_le

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
open Set Filter Topology
section General
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
theorem dual_apply_apply (g : G) (f : Module.Dual ℂ V) (v : V) :
    Representation.dual ρ g f v = f (ρ g⁻¹ v) := rfl
variable {ρ} in

theorem mem_fixedVectors_dual {H : Subgroup G} {f : Module.Dual ℂ V} :
    f ∈ fixedVectors (Representation.dual ρ) H ↔ ∀ h ∈ H, ∀ v, f (ρ h v) = f v := by
  constructor
  · intro hf h hh v
    have := LinearMap.congr_fun (hf h⁻¹ (inv_mem hh)) v
    rwa [dual_apply_apply, inv_inv] at this
  · intro hf h hh
    ext v
    rw [dual_apply_apply]
    exact hf _ (inv_mem hh) v
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {ρ} in

theorem mem_smoothVectors_of_mem_fixedVectors {H : Subgroup G} (hH : IsOpen (H : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ H) : v ∈ smoothVectors ρ :=
  Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hH
variable {ρ} in
theorem mem_fixedVectors_smoothPart {H : Subgroup G} {x : smoothVectors ρ} :
    x ∈ fixedVectors (smoothPart ρ) H ↔ (x : V) ∈ fixedVectors ρ H := by
  simp only [mem_fixedVectors, Subtype.ext_iff, coe_smoothPart_apply]
def contragredient : Representation ℂ G (smoothVectors (Representation.dual ρ)) :=
  smoothPart (Representation.dual ρ)
theorem contragredient_apply_apply (g : G) (x : smoothVectors (Representation.dual ρ)) (v : V) :
    ((contragredient ρ g x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      (x : Module.Dual ℂ V) (ρ g⁻¹ v) := rfl
variable {ρ} in
theorem mem_fixedVectors_contragredient {H : Subgroup G}
    {x : smoothVectors (Representation.dual ρ)} :
    x ∈ fixedVectors (contragredient ρ) H ↔
      ∀ h ∈ H, ∀ v, (x : Module.Dual ℂ V) (ρ h v) = (x : Module.Dual ℂ V) v :=
  mem_fixedVectors_smoothPart.trans mem_fixedVectors_dual
def restrictFixed (H : Subgroup G) :
    fixedVectors (contragredient ρ) H →ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ H) :=
  (fixedVectors ρ H).subtype.dualMap ∘ₗ (smoothVectors (Representation.dual ρ)).subtype ∘ₗ
    (fixedVectors (contragredient ρ) H).subtype
def evalSmooth : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual ρ)) :=
  (smoothVectors (Representation.dual ρ)).subtype.dualMap ∘ₗ Module.Dual.eval ℂ V
theorem evalSmooth_apply (v : V) (x : smoothVectors (Representation.dual ρ)) :
    evalSmooth ρ v x = (x : Module.Dual ℂ V) v := rfl
variable {ρ} in

theorem evalSmooth_mem {v : V} (hv : v ∈ smoothVectors ρ) :
    evalSmooth ρ v ∈ smoothVectors (Representation.dual (contragredient ρ)) := by
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v) (fun g hg => ?_) hv
  rw [mem_stabilizerOf] at hg ⊢
  ext x
  rw [dual_apply_apply, evalSmooth_apply, evalSmooth_apply, contragredient_apply_apply, inv_inv,
    hg]
variable {ρ} in

def toDoubleContragredient (hρ : IsSmooth ρ) :
    Representation.IntertwiningMap ρ (contragredient (contragredient ρ)) where
  toLinearMap := (evalSmooth ρ).codRestrict _ fun v => evalSmooth_mem (hρ v)
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun x => ?_)
    change (x : Module.Dual ℂ V) (ρ g v) = (x : Module.Dual ℂ V) (ρ g⁻¹⁻¹ v)
    rw [inv_inv]
end General
section LocallyProfinite
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
def extendFixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (μ : Module.Dual ℂ (fixedVectors ρ K)) : fixedVectors (contragredient ρ) K :=
  have hinv : ∀ k ∈ K, ∀ v, (μ ∘ₗ fixedProj ρ hρ hKc hKo) (ρ k v) =
      (μ ∘ₗ fixedProj ρ hρ hKc hKo) v := fun k hk v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fixedProj_apply_act hρ hKc hKo hk]
  ⟨⟨μ ∘ₗ fixedProj ρ hρ hKc hKo,
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hinv)⟩,
    mem_fixedVectors_contragredient.2 hinv⟩
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
theorem restrictFixed_bijective : Function.Bijective (restrictFixed ρ K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) = 0 :=
      eq_of_invariant_of_eqOn hρ hKc hKo (mem_fixedVectors_contragredient.1 x.2)
        (fun _ _ _ => rfl) fun v hv => LinearMap.congr_fun hx ⟨v, hv⟩
    exact Subtype.ext (Subtype.ext hx')
  · intro μ
    refine ⟨extendFixed hρ hKc hKo μ, LinearMap.ext fun v => ?_⟩
    change μ (fixedProj ρ hρ hKc hKo v) = μ v
    rw [Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo v.2)]
def fixedContragredientEquiv :
    fixedVectors (contragredient ρ) K ≃ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ K) :=
  LinearEquiv.ofBijective (restrictFixed ρ K) (restrictFixed_bijective hρ hKc hKo)
end LocallyProfinite
section Admissible
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
end Admissible
end GroundTheory.Automorphic


