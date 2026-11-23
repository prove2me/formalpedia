-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:50.180295+00:00
-- url     : https://prove2.me/theorems/ca9b2656-4ea1-4d53-97e5-a8e009e5e705
-- title:
--   Additive Defs
-- statement:
--   Definitions and structural lemmas for Additive Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
universe u v
open Representation
abbrev TorsN (A : Type*) [AddCommGroup A] (n : ℕ) : Type _ :=
  ↥(LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)))
theorem mem_ker_lsmul_iff {A : Type*} [AddCommGroup A] (n : ℕ) (x : A) :
    x ∈ LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)) ↔ n • x = 0 := by
  simp
theorem TorsN.nsmul_eq_zero {A : Type*} [AddCommGroup A] {n : ℕ} (x : TorsN A n) :
    n • x = 0 :=
  Subtype.ext (by simpa using (mem_ker_lsmul_iff n (x : A)).1 x.2)
instance TorsN.instModule (A : Type*) [AddCommGroup A] (n : ℕ) : Module (ZMod n) (TorsN A n) :=
  AddCommGroup.zmodModule TorsN.nsmul_eq_zero
instance additiveDistribMulAction {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] :
    DistribMulAction Γ (Additive M) where
  smul γ a := Additive.ofMul (γ • a.toMul)
  one_smul a := congrArg Additive.ofMul (one_smul Γ a.toMul)
  mul_smul γ δ a := congrArg Additive.ofMul (mul_smul γ δ a.toMul)
  smul_zero γ := congrArg Additive.ofMul (smul_one γ)
  smul_add γ a b := congrArg Additive.ofMul (smul_mul' γ a.toMul b.toMul)
@[simp]
theorem toMul_smul_additive {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] (γ : Γ)
    (a : Additive M) : (γ • a).toMul = γ • a.toMul :=
  rfl
@[simp]
theorem smul_ofMul_additive {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] (γ : Γ)
    (a : M) : γ • Additive.ofMul a = Additive.ofMul (γ • a) :=
  rfl
section Rep
def piRep {k Γ X : Type*} [CommSemiring k] [Monoid Γ] [AddCommMonoid X] [Module k X] (ι : Type*)
    (ρ : Representation k Γ X) : Representation k Γ (ι → X) where
  toFun γ := LinearMap.pi fun i => ρ γ ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' γ δ := by ext; simp
@[simp]
theorem piRep_apply {k Γ X : Type*} [CommSemiring k] [Monoid Γ] [AddCommMonoid X] [Module k X]
    (ι : Type*) (ρ : Representation k Γ X) (γ : Γ) (x : ι → X) (i : ι) :
    piRep ι ρ γ x i = ρ γ (x i) :=
  rfl
variable {Γ : Type*} [Group Γ]
def intRepToZMod (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ρ : Representation ℤ Γ V) : Representation (ZMod n) Γ V where
  toFun γ := (ρ γ).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp
@[simp]
theorem intRepToZMod_apply (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ρ : Representation ℤ Γ V) (γ : Γ) (x : V) : intRepToZMod n ρ γ x = ρ γ x :=
  rfl
variable (Γ) (A : Type*) [AddCommGroup A] [DistribMulAction Γ A] (n : ℕ)
theorem range_lsmul_le_comap (γ : Γ) :
    LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ))).comap (ofDistribMulAction ℤ Γ A γ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨γ • x, by simp⟩
theorem ker_lsmul_le_comap (γ : Γ) :
    LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).comap (ofDistribMulAction ℤ Γ A γ) := by
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_comap,
    ofDistribMulAction_apply_apply] at hx ⊢
  rw [← smul_comm γ (n : ℤ) x, hx, smul_zero]
noncomputable def modNRep : Representation (ZMod n) Γ (ModN A n) :=
  intRepToZMod n ((ofDistribMulAction ℤ Γ A).quotient _ (range_lsmul_le_comap Γ A n))
def torsNRep : Representation (ZMod n) Γ (TorsN A n) :=
  intRepToZMod n ((ofDistribMulAction ℤ Γ A).subrepresentation _ (ker_lsmul_le_comap Γ A n))
end Rep
structure AdditiveFunction (l : ℕ) (Γ : Type v) [Group Γ] where

  toFun : ∀ (X : Type u) [AddCommGroup X] [Module (ZMod l) X] [Finite X],
    Representation (ZMod l) Γ X → ℤ

  additive : ∀ {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module (ZMod l) X₁] [Finite X₁]
    [AddCommGroup X₂] [Module (ZMod l) X₂] [Finite X₂]
    [AddCommGroup X₃] [Module (ZMod l) X₃] [Finite X₃]
    (ρ₁ : Representation (ZMod l) Γ X₁) (ρ₂ : Representation (ZMod l) Γ X₂)
    (ρ₃ : Representation (ZMod l) Γ X₃) (f : X₁ →ₗ[ZMod l] X₂) (g : X₂ →ₗ[ZMod l] X₃),
    ρ₁.IsIntertwiningMap ρ₂ f → ρ₂.IsIntertwiningMap ρ₃ g →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    toFun X₂ ρ₂ = toFun X₁ ρ₁ + toFun X₃ ρ₃
namespace AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
noncomputable def g (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] : ℤ :=
  open Classical in
  if h : Finite (ModN A l) ∧ Finite (TorsN A l) then
    haveI := h.1
    haveI := h.2
    d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l)
  else 0
noncomputable def one [NeZero l] : ℤ :=
  d.toFun (ULift.{u} (ZMod l)) (Representation.trivial (ZMod l) Γ (ULift.{u} (ZMod l)))
end AdditiveFunction
end GroundTheory.ProfCoh


