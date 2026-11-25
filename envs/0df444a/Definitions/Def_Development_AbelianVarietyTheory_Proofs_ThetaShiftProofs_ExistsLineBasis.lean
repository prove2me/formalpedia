-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:31.513815+00:00
-- url     : https://prove2.me/theorems/154e93a8-8ea8-412a-b2bd-a787f8040c30
-- title:
--   Exists Line Basis
-- statement:
--   Definitions and structural lemmas for Exists Line Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsLineBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]
noncomputable def cmEquiv (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Ψ ⊕ Ψ ≃ (E →+* ℂ) :=
  Equiv.ofBijective (Sum.elim (fun τ => τ.1) (fun τ => ComplexEmbedding.conjugate τ.1)) <| by
    have cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · exact congrArg _ (Subtype.ext h)
      · exact absurd (h ▸ a.2) ((hΨ _).1 b.2)
      · exact absurd (h ▸ b.2) ((hΨ _).1 a.2)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [cc, cc] at this
        exact congrArg _ (Subtype.ext this)
    · intro τ
      by_cases h : τ ∈ Ψ
      · exact ⟨.inl ⟨τ, h⟩, rfl⟩
      · refine ⟨.inr ⟨ComplexEmbedding.conjugate τ, ?_⟩, cc τ⟩
        by_contra h'
        exact h ((hΨ τ).2 h')
end GlobalTheory.LatticeCovolumeL2


