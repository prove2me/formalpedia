-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinDefs
-- name    : GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:23.756812+00:00
-- url     : https://prove2.me/theorems/9d09fc53-9ca1-41b1-b668-1d347776c99f
-- title:
--   Artin Defs
-- statement:
--   Definitions and structural lemmas for Artin Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open Representation
open scoped TensorProduct
universe u v
section Fun
variable {k Γ N : Type*} [CommSemiring k] [Group Γ] [AddCommMonoid N] [Module k N]
def funRep (Y : Type*) [MulAction Γ Y] (σ : Representation k Γ N) : Representation k Γ (Y → N) where
  toFun γ := LinearMap.pi fun y => σ γ ∘ₗ LinearMap.proj (γ⁻¹ • y)
  map_one' := by
    ext F y
    simp
  map_mul' γ δ := by
    ext F y
    simp [mul_smul]
@[simp]
theorem funRep_apply (Y : Type*) [MulAction Γ Y] (σ : Representation k Γ N) (γ : Γ) (F : Y → N)
    (y : Y) : funRep Y σ γ F y = σ γ (F (γ⁻¹ • y)) :=
  rfl
end Fun
section Pi
variable {k Γ : Type*} [CommSemiring k] [Monoid Γ]
def piFamilyRep {ι : Type*} (V : ι → Type*) [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k Γ (V i)) : Representation k Γ (∀ i, V i) where
  toFun γ := LinearMap.pi fun i => ρ i γ ∘ₗ LinearMap.proj i
  map_one' := by
    ext
    simp
  map_mul' γ δ := by
    ext
    simp
end Pi
theorem finite_tensorProduct_zmod (l : ℕ) [NeZero l] (W N : Type*) [AddCommGroup W]
    [Module (ZMod l) W] [Finite W] [AddCommGroup N] [Module (ZMod l) N] [Finite N] :
    Finite (W ⊗[ZMod l] N) := by
  have := Module.Finite.of_finite (R := ZMod l) (M := W)
  have := Module.Finite.of_finite (R := ZMod l) (M := N)
  exact Module.finite_of_finite (ZMod l)
namespace AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ]
noncomputable def tensorRep [Fact l.Prime] (d : AdditiveFunction.{u} l Γ) {N : Type u}
    [AddCommGroup N] [Module (ZMod l) N] [Finite N] (σ : Representation (ZMod l) Γ N) :
    AdditiveFunction.{u} l Γ where
  toFun W _ _ _ ρ :=
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    haveI := finite_tensorProduct_zmod l W N
    d.toFun (W ⊗[ZMod l] N) (ρ.tprod σ)
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    have := finite_tensorProduct_zmod l X₁ N
    have := finite_tensorProduct_zmod l X₂ N
    have := finite_tensorProduct_zmod l X₃ N
    exact d.additive _ _ _ (f.rTensor N) (g.rTensor N)
      (isIntertwiningMap_rTensor σ hf) (isIntertwiningMap_rTensor σ hg)
      (Module.Flat.rTensor_preserves_injective_linearMap f hinj) (rTensor_exact N hfg hs)
      (LinearMap.rTensor_surjective N hs)
end AdditiveFunction
end GroundTheory.ProfCoh


