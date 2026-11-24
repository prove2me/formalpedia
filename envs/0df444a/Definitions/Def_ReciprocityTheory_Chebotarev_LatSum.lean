-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
-- name    : ReciprocityTheory_Chebotarev_LatSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:51.85703+00:00
-- url     : https://prove2.me/theorems/ff19e3ed-c5ab-458e-ad29-346fb0b566dd
-- title:
--   Lat Sum
-- statement:
--   Definitions and structural lemmas for Lat Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/LatSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
namespace ReciprocityTheory.Cheb
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
noncomputable def latSumEquiv (Λ₀ Λ' : Submodule ℤ V) (hle : Λ' ≤ Λ₀) (reps : Finset V)
    (hmem : ∀ β ∈ reps, β ∈ Λ₀)
    (hcover : ∀ α ∈ Λ₀, ∃ l ∈ Λ', ∃ β ∈ reps, α = l + β)
    (huniq : ∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ Λ' → β₁ = β₂) :
    Λ' × reps ≃ Λ₀ :=
  Equiv.ofBijective (fun p => ⟨(p.1 : V) + (p.2 : V), Λ₀.add_mem (hle p.1.2) (hmem _ p.2.2)⟩) (by
    constructor
    · rintro ⟨l₁, β₁⟩ ⟨l₂, β₂⟩ h
      simp only [Subtype.mk.injEq] at h
      have hβ : (β₁ : V) = β₂ := huniq _ β₁.2 _ β₂.2 (by
        have e : (β₁ : V) - β₂ = l₂ - l₁ := by
          rw [sub_eq_sub_iff_add_eq_add, add_comm (β₁ : V), h]
        rw [e]; exact Λ'.sub_mem l₂.2 l₁.2)
      have hl : (l₁ : V) = l₂ := by rw [hβ] at h; exact add_right_cancel h
      exact Prod.ext (Subtype.ext hl) (Subtype.ext hβ)
    · rintro ⟨α, hα⟩
      obtain ⟨l, hl, β, hβ, rfl⟩ := hcover α hα
      exact ⟨(⟨l, hl⟩, ⟨β, hβ⟩), rfl⟩)
variable [FiniteDimensional ℝ V]
end ReciprocityTheory.Cheb


