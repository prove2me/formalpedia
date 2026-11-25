-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:46.95384+00:00
-- url     : https://prove2.me/theorems/902d86d2-f0a7-415f-b4cf-aa62ca12fe2e
-- title:
--   Has Comp Of Surjective
-- statement:
--   Definitions and structural lemmas for Has Comp Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasCompOfSurjective.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv


set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
namespace GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
theorem rep_mul (ρ : Representation ℂ Γ V) (a b : Γ) (v : V) : ρ a (ρ b v) = ρ (a * b) v := by
  rw [map_mul, Module.End.mul_apply]
def cut (e : Γ →* Γ) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) : Γ →* Γ where
  toFun g := (e g)⁻¹ * g
  map_one' := by simp
  map_mul' a b := by
    have h := (hc a b).inv_right.eq
    rw [map_mul, mul_inv_rev]
    calc (e b)⁻¹ * (e a)⁻¹ * (a * b) = (e b)⁻¹ * ((e a)⁻¹ * a) * b := by group
      _ = _ := by rw [← h]; group
def homSp (σ : Representation ℂ Γ W) (ρ : Representation ℂ Γ V) (e : Γ →* Γ) : Submodule ℂ (W →ₗ[ℂ] V) where
  carrier := {f | ∀ g x, f (σ g x) = ρ (e g) (f x)}
  add_mem' := fun {a b} ha hb g x => by simp [ha g x, hb g x]
  zero_mem' := fun g x => by simp
  smul_mem' := fun c f hf g x => by simp [hf g x]
def homRep (σ : Representation ℂ Γ W) (ρ : Representation ℂ Γ V) (e : Γ →* Γ)
    (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y)) : Representation ℂ Γ (homSp σ ρ e) where
  toFun g :=
    { toFun := fun f => ⟨ρ (cut e hc g) ∘ₗ f.1, fun y x => by
        simp only [LinearMap.comp_apply]
        rw [f.2 y x, rep_mul, rep_mul]
        exact congrArg (fun z => ρ z (f.1 x)) (hc g y).eq⟩
      map_add' := fun a b => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c a => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun x => by simp)
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun x => by simp)
def HasComp (ρ : Representation ℂ Γ V) (e : Γ →* Γ) (L : Subgroup Γ) (d : ℕ) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ Γ W), σ.IsIrreducible ∧
    (∀ T : End ℂ W, (∀ g, T * σ g = σ g * T) → ∃ c : ℂ, T = c • 1) ∧ (∀ g, σ (e g) = σ g) ∧
    (∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ g x) = ρ (e g) (f x)) ∧ finrank ℂ (fixed σ L) = d
section Family
variable {ι : Type} {e : ι → Γ →* Γ} {L : Subgroup Γ}
end Family
end GlobalTheory.BCT.DimFac


