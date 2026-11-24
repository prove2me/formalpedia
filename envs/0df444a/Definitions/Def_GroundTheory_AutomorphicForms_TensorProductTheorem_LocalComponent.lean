-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:19.085289+00:00
-- url     : https://prove2.me/theorems/edc67778-4014-4455-aed7-e0d058d90ec5
-- title:
--   Local Component
-- statement:
--   Definitions and structural lemmas for Local Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
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
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
section General
variable (σ) in

def genSubrep (N : Submodule ℂ V) : Subrepresentation σ where
  toSubmodule := ⨆ g : L, N.map (σ g)
  apply_mem_toSubmodule g x hx := by
    have : (⨆ h : L, N.map (σ h)) ≤ (⨆ h : L, N.map (σ h)).comap (σ g) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact Submodule.mem_iSup_of_mem (g * h) ⟨n, hn, rfl⟩
    exact this hx
theorem mem_genSubrep_of_mem {N : Submodule ℂ V} {n : V} (hn : n ∈ N) (g : L) :
    σ g n ∈ (genSubrep σ N).toSubmodule :=
  Submodule.mem_iSup_of_mem g ⟨n, hn, rfl⟩
theorem le_genSubrep (N : Submodule ℂ V) : N ≤ (genSubrep σ N).toSubmodule := fun n hn => by
  simpa using mem_genSubrep_of_mem (σ := σ) hn 1
end General
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
def genKernel : Submodule ℂ (genSubrep σ N).toSubmodule where
  carrier := {u | ∀ g, fixedProj σ hσ hKc hKo (σ g u) = 0}
  add_mem' {a b} ha hb g := by
    simp only [mem_setOf_eq, Submodule.coe_add, map_add, ha g, hb g, add_zero]
  zero_mem' g := by simp
  smul_mem' c a ha g := by
    simp only [mem_setOf_eq, Submodule.coe_smul, map_smul, ha g, smul_zero]
theorem genKernel_le_comap (g : L) :
    genKernel hσ hKc hKo N ≤
      (genKernel hσ hKc hKo N).comap ((genSubrep σ N).toRepresentation g) := by
  intro u hu h
  show fixedProj σ hσ hKc hKo (σ h (σ g u)) = 0
  rw [← Module.End.mul_apply, ← map_mul]
  exact hu (h * g)
def genQuotRep : Representation ℂ L ((genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N) :=
  (genSubrep σ N).toRepresentation.quotient _ (genKernel_le_comap hσ hKc hKo N)
def genQuotMk : N →ₗ[ℂ] (genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N :=
  (genKernel hσ hKc hKo N).mkQ ∘ₗ Submodule.inclusion (le_genSubrep N)
def genQuotMap : Representation.IntertwiningMap (genSubrep σ N).toRepresentation
    (genQuotRep hσ hKc hKo N) where
  toLinearMap := (genKernel hσ hKc hKo N).mkQ
  isIntertwining' g := LinearMap.ext fun _ => rfl
variable {N}
section Simple
variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)
end Simple
def genQuotForm (l : Dual ℂ (fixedVectors σ K)) :
    Dual ℂ ((genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N) :=
  (genKernel hσ hKc hKo N).liftQ (l ∘ₗ fixedProj σ hσ hKc hKo ∘ₗ (genSubrep σ N).toSubmodule.subtype)
    fun u hu => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
      have := hu 1
      rw [map_one, Module.End.one_apply] at this
      simp only [Submodule.subtype_apply, this, map_zero]
end RestrictedTensor
end GroundTheory.Automorphic


