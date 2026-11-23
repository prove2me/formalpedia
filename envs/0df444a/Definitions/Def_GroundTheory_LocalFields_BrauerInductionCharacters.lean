-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
-- name    : GroundTheory_LocalFields_BrauerInductionCharacters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:06.436646+00:00
-- url     : https://prove2.me/theorems/2ac36a75-98e5-44d2-aada-d4532068ded4
-- title:
--   Brauer Induction Characters
-- statement:
--   Definitions and structural lemmas for Brauer Induction Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open Module Representation
section Transport
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def conjRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W where
  toFun g := e.conj (ρ g)
  map_one' := by
    ext w
    simp [LinearEquiv.conj_apply]
  map_mul' g h := by
    ext w
    simp [LinearEquiv.conj_apply]
theorem conjRep_apply (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (g : G) (w : W) :
    conjRep ρ e g w = e (ρ g (e.symm w)) := by
  simp [conjRep, LinearEquiv.conj_apply]
def conjRepEquiv (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation.Equiv ρ (conjRep ρ e) :=
  Representation.Equiv.mk e fun g ↦ by
    ext v
    simp [conjRep_apply]
def subrepOrderIso {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : Representation.Equiv ρ σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U := ⟨U.toSubmodule.map (φ.toLinearEquiv : V →ₗ[ℂ] W), by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨ρ g v, U.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v⟩
  invFun U := ⟨U.toSubmodule.map (φ.toLinearEquiv.symm : W →ₗ[ℂ] V), by
    rintro g _ ⟨w, hw, rfl⟩
    refine ⟨σ g w, U.apply_mem_toSubmodule g hw, ?_⟩
    apply φ.toLinearEquiv.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g
      (φ.toLinearEquiv.symm w)
    rw [show φ.toIntertwiningMap (φ.toLinearEquiv.symm w) = w from
      φ.toLinearEquiv.apply_symm_apply w] at this
    exact this.symm⟩
  left_inv U := by
    apply Subrepresentation.ext
    change (U.toSubmodule.map (φ.toLinearEquiv : V →ₗ[ℂ] W)).map
      (φ.toLinearEquiv.symm : W →ₗ[ℂ] V) = U.toSubmodule
    rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
  right_inv U := by
    apply Subrepresentation.ext
    change (U.toSubmodule.map (φ.toLinearEquiv.symm : W →ₗ[ℂ] V)).map
      (φ.toLinearEquiv : V →ₗ[ℂ] W) = U.toSubmodule
    rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]
  map_rel_iff' {U U'} := by
    change U.toSubmodule.map _ ≤ U'.toSubmodule.map _ ↔ U.toSubmodule ≤ U'.toSubmodule
    exact Submodule.map_le_map_iff_of_injective φ.toLinearEquiv.injective _ _
end Transport
section Inner
variable {G : Type*} [Group G] [Fintype G]
variable (G) in

def charInner : (G → ℂ) →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun χ ψ ↦ (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * ψ g⁻¹)
    (fun χ χ' ψ ↦ by simp [add_mul, Finset.sum_add_distrib, mul_add])
    (fun c χ ψ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring)
    (fun χ ψ ψ' ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun c χ ψ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring)
theorem charInner_apply (χ ψ : G → ℂ) :
    charInner G χ ψ = (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * ψ g⁻¹ := rfl
def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g
end Inner
section Characters
universe u
variable {G : Type*} [Group G] [Fintype G]
def IsCharacter (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.character = χ
def IsIrrCharacter (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ
section Rep
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
end Rep
theorem charInner_of_isIrrCharacter {χ ψ : G → ℂ} (hχ : IsIrrCharacter χ) (hψ : IsIrrCharacter ψ) :
    charInner G χ ψ = if χ = ψ then 1 else 0 := by
  classical
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hχ
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := hψ
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h1 := char_orthonormal ρ σ
  have h2 := char_orthonormal ρ ρ
  rw [← charInner_apply] at h1 h2
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h2
  rw [h1]
  by_cases he : Nonempty (Representation.Equiv σ ρ)
  · rw [if_pos he, if_pos (char_iso he.some).symm]
  · have hne : ρ.character ≠ σ.character := by
      intro heq
      rw [if_neg he, ← heq, h2] at h1
      simp at h1
    rw [if_neg he, if_neg hne]
theorem finite_setOf_isIrrCharacter : {χ : G → ℂ | IsIrrCharacter χ}.Finite := by
  classical
  apply LinearIndependent.setFinite (R := ℂ)
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h := congrArg (fun f ↦ charInner G f i.1) hs
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · rw [charInner_of_isIrrCharacter i.2 i.2, if_pos rfl, smul_eq_mul, mul_one] at h
    exact h
  · intro j _ hj
    rw [charInner_of_isIrrCharacter j.2 i.2, if_neg fun h ↦ hj (Subtype.ext h), smul_zero]
  · intro hi'
    exact absurd hi hi'
variable (G) in

def irrChars : Finset (G → ℂ) := finite_setOf_isIrrCharacter.toFinset
end Characters
section Regular
variable {G : Type*} [Group G] [Fintype G]
end Regular
section Completeness
variable {G : Type*} [Group G] [Fintype G]
end Completeness
section Closure
variable {G : Type*} [Group G]
variable [Fintype G]
end Closure
end GroundTheory.LocalField


