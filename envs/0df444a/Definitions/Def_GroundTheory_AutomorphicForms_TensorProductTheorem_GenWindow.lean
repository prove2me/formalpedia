-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:54.87755+00:00
-- url     : https://prove2.me/theorems/76dbe80c-038f-425d-aa7b-2041facf56f2
-- title:
--   Gen Window
-- statement:
--   Definitions and structural lemmas for Gen Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
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
namespace RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
section Orbit
def mOrbitSpan (ρ : Representation ℂ M V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (range fun m => ρ m v)
  apply_mem_toSubmodule g x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
def mOrbitMap (ρ : Representation ℂ M V) (v : V) : (M →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun m => ρ m v
end Orbit
section Window
variable (ρ : Representation ℂ M V)
structure IsWinProj (e : End ℂ V) : Prop where
  idem : ∀ v, e (e v) = e v
  mem : ∀ Y : Subrepresentation ρ, ∀ y ∈ Y.toSubmodule, e y ∈ Y.toSubmodule
variable {ρ} {e : End ℂ V}
variable (ρ e) in

def winOp (m : M) : End ℂ (LinearMap.range e) :=
  LinearMap.codRestrict (LinearMap.range e) (e ∘ₗ ρ m ∘ₗ (LinearMap.range e).subtype)
    fun x => ⟨_, rfl⟩
variable (ρ e) in

def winOps : Set (End ℂ (LinearMap.range e)) := range (winOp ρ e)
end Window
section Quotient
variable (ρ : Representation ℂ M V)
def mGenSubrep (N : Submodule ℂ V) : Subrepresentation ρ where
  toSubmodule := ⨆ g : M, N.map (ρ g)
  apply_mem_toSubmodule g x hx := by
    have : (⨆ h : M, N.map (ρ h)) ≤ (⨆ h : M, N.map (ρ h)).comap (ρ g) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact Submodule.mem_iSup_of_mem (g * h) ⟨n, hn, rfl⟩
    exact this hx
theorem le_mGenSubrep (N : Submodule ℂ V) : N ≤ (mGenSubrep ρ N).toSubmodule := fun n hn =>
  Submodule.mem_iSup_of_mem 1 ⟨n, hn, by simp⟩
variable (e : End ℂ V) (N : Submodule ℂ V)
def mGenKernel : Submodule ℂ (mGenSubrep ρ N).toSubmodule where
  carrier := {u | ∀ g, e (ρ g u) = 0}
  add_mem' {a b} ha hb g := by
    simp only [mem_setOf_eq, Submodule.coe_add, map_add, ha g, hb g, add_zero]
  zero_mem' g := by simp
  smul_mem' c a ha g := by
    simp only [mem_setOf_eq, Submodule.coe_smul, map_smul, ha g, smul_zero]
theorem mGenKernel_le_comap (g : M) :
    mGenKernel ρ e N ≤ (mGenKernel ρ e N).comap ((mGenSubrep ρ N).toRepresentation g) := by
  intro u hu h
  show e (ρ h (ρ g u)) = 0
  rw [show ρ h (ρ g u) = ρ (h * g) u by rw [map_mul]; rfl]
  exact hu (h * g)
def mGenQuotRep : Representation ℂ M ((mGenSubrep ρ N).toSubmodule ⧸ mGenKernel ρ e N) :=
  (mGenSubrep ρ N).toRepresentation.quotient _ (mGenKernel_le_comap ρ e N)
def mGenQuotMk : N →ₗ[ℂ] (mGenSubrep ρ N).toSubmodule ⧸ mGenKernel ρ e N :=
  (mGenKernel ρ e N).mkQ ∘ₗ Submodule.inclusion (le_mGenSubrep ρ N)
variable {ρ e N}
variable (ρ e N) in

def mGenQuotForm (l : Dual ℂ V) :
    Dual ℂ ((mGenSubrep ρ N).toSubmodule ⧸ mGenKernel ρ e N) :=
  (mGenKernel ρ e N).liftQ (l ∘ₗ e ∘ₗ (mGenSubrep ρ N).toSubmodule.subtype) fun u hu => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
    have := hu 1
    rw [map_one, Module.End.one_apply] at this
    simp only [Submodule.subtype_apply, this, map_zero]
end Quotient
end RestrictedTensor
end GroundTheory.Automorphic


