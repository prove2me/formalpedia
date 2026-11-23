-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:31.93981+00:00
-- url     : https://prove2.me/theorems/6679c435-f806-4015-becf-30fa86b2b26e
-- title:
--   Additive Snake
-- statement:
--   Definitions and structural lemmas for Additive Snake, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/AdditiveSnake.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
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
universe u v
open Representation
section Intertwining
variable {k Γ X Y : Type*} [CommRing k] [Monoid Γ] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] {ρ : Representation k Γ X} {σ : Representation k Γ Y}
  {φ : X →ₗ[k] Y}
theorem ker_le_comap_of_isIntertwiningMap (hφ : ρ.IsIntertwiningMap σ φ) (γ : Γ) :
    LinearMap.ker φ ≤ (LinearMap.ker φ).comap (ρ γ) := fun x hx => by
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
  rw [hφ.isIntertwining, hx, map_zero]
theorem range_le_comap_of_isIntertwiningMap (hφ : ρ.IsIntertwiningMap σ φ) (γ : Γ) :
    LinearMap.range φ ≤ (LinearMap.range φ).comap (σ γ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ρ γ x, hφ.isIntertwining γ x⟩
end Intertwining
namespace AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
section Basic
variable {X Y : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
  [AddCommGroup Y] [Module (ZMod l) Y] [Finite Y]
end Basic
end AdditiveFunction
instance modN_finite (A : Type*) [AddCommGroup A] [Finite A] (n : ℕ) : Finite (ModN A n) :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
section Maps
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)
def torsNMap (f : A →+ B) : TorsN A n →ₗ[ZMod n] TorsN B n :=
  (f.toIntLinearMap.restrict (p := LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)))
    (q := LinearMap.ker (LinearMap.lsmul ℤ B (n : ℤ))) (fun x hx => by
      rw [mem_ker_lsmul_iff] at hx ⊢
      simp [← map_nsmul, hx])).toAddMonoidHom.toZModLinearMap n
@[simp]
theorem coe_torsNMap_apply (f : A →+ B) (x : TorsN A n) :
    ((torsNMap n f x : TorsN B n) : B) = f x :=
  rfl
def modNMap (f : A →+ B) : ModN A n →ₗ[ZMod n] ModN B n :=
  (Submodule.mapQ _ _ f.toIntLinearMap (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)).toAddMonoidHom.toZModLinearMap n
@[simp]
theorem modNMap_mk (f : A →+ B) (x : A) :
    modNMap n f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  rfl
section Connecting
variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)
noncomputable def connectingFun (c : TorsN C n) : ModN A n :=
  Submodule.Quotient.mk (Function.invFun f (n • Function.surjInv hh (c : C)))
variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh
theorem exists_lift (c : TorsN C n) : ∃ b a, h b = c ∧ f a = n • b := by
  refine ⟨Function.surjInv hh (c : C), Function.invFun f (n • Function.surjInv hh (c : C)),
    Function.surjInv_eq hh _, Function.invFun_eq ?_⟩
  refine (hfh _).1 ?_
  rw [map_nsmul, Function.surjInv_eq hh]
  exact (mem_ker_lsmul_iff n (c : C)).1 c.2
variable (hf : Function.Injective f)
include hf
theorem connectingFun_spec (c : TorsN C n) (b : B) (a : A) (hb : h b = c) (ha : f a = n • b) :
    connectingFun f h hh c = Submodule.Quotient.mk a := by
  have h₀ : f (Function.invFun f (n • Function.surjInv hh (c : C))) =
      n • Function.surjInv hh (c : C) :=
    Function.invFun_eq (by
      refine (hfh _).1 ?_
      rw [map_nsmul, Function.surjInv_eq hh]
      exact (mem_ker_lsmul_iff n (c : C)).1 c.2)
  obtain ⟨a₁, ha₁⟩ := (hfh (b - Function.surjInv hh (c : C))).1 (by
    rw [map_sub, hb, Function.surjInv_eq hh, sub_self])
  have key : a - Function.invFun f (n • Function.surjInv hh (c : C)) = n • a₁ := hf (by
    rw [map_sub, ha, h₀, map_nsmul, ha₁, smul_sub])
  rw [connectingFun, Submodule.Quotient.eq]
  exact ⟨-a₁, by simp [← key]⟩
theorem connectingFun_zero : connectingFun f h hh (0 : TorsN C n) = 0 := by
  rw [connectingFun_spec hh hfh hf 0 0 0 (by simp) (by simp)]
  rfl
theorem connectingFun_add (c c' : TorsN C n) :
    connectingFun f h hh (c + c') = connectingFun f h hh c + connectingFun f h hh c' := by
  obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
  obtain ⟨b', a', hb', ha'⟩ := exists_lift hh hfh c'
  rw [connectingFun_spec hh hfh hf c b a hb ha, connectingFun_spec hh hfh hf c' b' a' hb' ha',
    connectingFun_spec hh hfh hf (c + c') (b + b') (a + a') (by simp [hb, hb'])
      (by simp [ha, ha', smul_add])]
  rfl
noncomputable def connecting : TorsN C n →ₗ[ZMod n] ModN A n :=
  AddMonoidHom.toZModLinearMap n
    { toFun := connectingFun f h hh
      map_zero' := connectingFun_zero hh hfh hf
      map_add' := connectingFun_add hh hfh hf }
end Connecting
end Maps
section Equivariant
variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)
end Equivariant
section Finiteness
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] {n : ℕ}
  {f : A →+ B} {h : B →+ C}
end Finiteness
section Actions
variable {Γ : Type*} [Monoid Γ] {A : Type*} [AddCommGroup A] [DistribMulAction Γ A]
abbrev subgroupDistribMulAction (H : AddSubgroup A) (hH : ∀ (γ : Γ) (a : A), a ∈ H → γ • a ∈ H) :
    DistribMulAction Γ H where
  smul γ a := ⟨γ • (a : A), hH γ a a.2⟩
  one_smul a := Subtype.ext (one_smul Γ (a : A))
  mul_smul γ δ a := Subtype.ext (mul_smul γ δ (a : A))
  smul_zero γ := Subtype.ext (smul_zero γ)
  smul_add γ a b := Subtype.ext (smul_add γ (a : A) b)
abbrev quotientDistribMulAction (H : AddSubgroup A) (hH : ∀ (γ : Γ) (a : A), a ∈ H → γ • a ∈ H) :
    DistribMulAction Γ (A ⧸ H) where
  smul γ := QuotientAddGroup.map H H (DistribSMul.toAddMonoidHom A γ) (fun a ha => hH γ a ha)
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (one_smul Γ a)
  mul_smul γ δ x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (mul_smul γ δ a)
  smul_zero γ := map_zero _
  smul_add γ x y := map_add _ x y
end Actions
namespace AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
end AdditiveFunction
end GroundTheory.ProfCoh


