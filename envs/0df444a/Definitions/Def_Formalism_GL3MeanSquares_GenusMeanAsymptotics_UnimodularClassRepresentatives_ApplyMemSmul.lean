-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmul
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T09:24:41.216914+00:00
-- url     : https://prove2.me/theorems/e2afd4c5-29d6-49f3-ae52-f03d3095adfd
-- title:
--   Apply Mem Smul
-- statement:
--   Definitions and structural lemmas for Apply Mem Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmul.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.D2
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def pK (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Submodule (𝓞 K) K :=
  locF 𝔭 (Submodule.map (Algebra.linearMap (𝓞 K) K) (extP K 𝔭 ^ k))
def glSub (A : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {X | Formalism.HermitianLatticesTheory.gmap X A = A}
  one_mem' := autSub_gmap_one A
  mul_mem' := by
    intro a b ha hb
    show Formalism.HermitianLatticesTheory.gmap (a * b) A = A
    rw [autSub_gmap_mul, show Formalism.HermitianLatticesTheory.gmap b A = A from hb, show Formalism.HermitianLatticesTheory.gmap a A = A from ha]
  inv_mem' := by
    intro a ha
    show Formalism.HermitianLatticesTheory.gmap a⁻¹ A = A
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.gmap a A = A from ha]
    rw [← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
theorem apply_mem {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} (hX : X ∈ glSub A) {x : V} (hx : x ∈ A) :
    X x ∈ A := by
  have hX' : Formalism.HermitianLatticesTheory.gmap X A = A := hX
  rw [← hX']
  exact Submodule.mem_map_of_mem hx
theorem apply_mem_smul {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} (hX : X ∈ glSub A) (I : Ideal (𝓞 K))
    {x : V} (hx : x ∈ I • A) : X x ∈ I • A := by
  have h2 : A.map ((X : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hX
  have h1 : X x ∈ (I • A).map ((X : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hx
  rwa [Submodule.map_smul'', h2] at h1
def sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {X | X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k}
  one_mem' := ⟨one_mem _, fun x _ y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx y hy => ?_⟩
    have := (pK K 𝔭 k).add_mem (ha' _ (apply_mem hb hx) _ (apply_mem hb hy)) (hb' x hx y hy)
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx y hy => ?_⟩
    have := (pK K 𝔭 k).neg_mem (ha' _ (apply_mem (inv_mem ha) hx) _ (apply_mem (inv_mem ha) hy))
    have e : ∀ z : V, a (a⁻¹ z) = z := fun z => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    simpa [e] using this
def nSub (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Subgroup (V ≃ₗ[K] V) where
  carrier := {X | X ∈ glSub A ∧ ∀ x ∈ A, X x - x ∈ extP K 𝔭 ^ k • A}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have := (extP K 𝔭 ^ k • A).add_mem (apply_mem_smul ha _ (hb' x hx)) (ha' x hx)
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have := (extP K 𝔭 ^ k • A).neg_mem (apply_mem_smul (inv_mem ha) _ (ha' x hx))
    have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    simpa [e] using this
def endL (A A' : Submodule (𝓞 K) V) : AddSubgroup (V →ₗ[K] V) where
  carrier := {D | ∀ x ∈ A, D x ∈ A'}
  zero_mem' := fun x _ => by simp
  add_mem' := fun ha hb x hx => A'.add_mem (ha x hx) (hb x hx)
  neg_mem' := fun ha x hx => A'.neg_mem (ha x hx)
def sesqL (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    AddSubgroup (V →ₗ⋆[K] V →ₗ[K] K) where
  carrier := {s | ∀ x ∈ A, ∀ y ∈ A, s x y ∈ pK K 𝔭 k}
  zero_mem' := fun x _ y _ => by simp
  add_mem' := fun ha hb x hx y hy => (pK K 𝔭 k).add_mem (ha x hx y hy) (hb x hx y hy)
  neg_mem' := fun ha x hx y hy => (pK K 𝔭 k).neg_mem (ha x hx y hy)
def hermL (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    AddSubgroup (V →ₗ⋆[K] V →ₗ[K] K) where
  carrier := {s | (∀ x y, star (s x y) = s y x) ∧ ∀ x ∈ A, ∀ y ∈ A, s x y ∈ pK K 𝔭 k}
  zero_mem' := ⟨fun x y => by simp, fun x _ y _ => by simp⟩
  add_mem' := fun ha hb => ⟨fun x y => by simp [ha.1 x y, hb.1 x y],
    fun x hx y hy => (pK K 𝔭 k).add_mem (ha.2 x hx y hy) (hb.2 x hx y hy)⟩
  neg_mem' := fun ha => ⟨fun x y => by simp [ha.1 x y],
    fun x hx y hy => (pK K 𝔭 k).neg_mem (ha.2 x hx y hy)⟩
def nO (𝔭 : Ideal (𝓞 F)) (z : K) : ℕ :=
  ((pK K 𝔭 0).toAddSubgroup.map (AddMonoidHom.mulLeft z)).relIndex (pK K 𝔭 0).toAddSubgroup
end Formalism.HermitianLattices.Ext.L3.D2


