-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
-- name    : GroundTheory_LocalFields_BrauerInductionSpan
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:47:11.083177+00:00
-- url     : https://prove2.me/theorems/30f38cff-0a6b-4cba-be13-bb42683fa6e5
-- title:
--   Brauer Induction Span
-- statement:
--   Definitions and structural lemmas for Brauer Induction Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
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
open scoped Classical
section OneDim
variable {K : Type*} [Group K]
theorem isCharacter_monoidHom (l : K →* ℂˣ) : IsCharacter (fun k ↦ (l k : ℂ)) := by
  let ρ : Representation ℂ K ℂ :=
    { toFun := fun k ↦ (l k : ℂ) • LinearMap.id
      map_one' := by simp; rfl
      map_mul' := fun k k' ↦ by
        ext
        simp [mul_comm] }
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance, ρ, ?_⟩
  funext k
  simp [Representation.character, ρ, LinearMap.trace_id]
end OneDim
variable {G : Type*} [Group G] [Fintype G]
def indLin (K : Subgroup G) (l : K →* ℂˣ) : G → ℂ := indFun K.subtype (fun k ↦ (l k : ℂ))
theorem IsCharacter.indLin (K : Subgroup G) (l : K →* ℂˣ) : IsCharacter (indLin K l) :=
  (isCharacter_monoidHom l).indFun K.subtype
section Transport
variable {H H' : Type*} [Group H] [Fintype H] [Group H'] [Fintype H']
end Transport
section Spans
variable (E : Subgroup G → Prop)
def monomialSet : Set (G → ℂ) := {f | ∃ K : Subgroup G, E K ∧ ∃ l : K →* ℂˣ, f = indLin K l}
def spanZ : Submodule ℤ (G → ℂ) := Submodule.span ℤ (monomialSet E)
def spanA (ζ : ℂ) : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ {f | ∃ a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ), ∃ g ∈ spanZ E, f = a • g}
variable {E}
end Spans
section Mono
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hE hmono
end Mono
section Descent
variable {E : Subgroup G → Prop}
end Descent
end GroundTheory.LocalField


