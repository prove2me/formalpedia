-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:04.715126+00:00
-- url     : https://prove2.me/theorems/5129bef7-aa07-4560-9fa0-859fdfb95bcd
-- title:
--   Mem Iff Conjugate Not Mem
-- statement:
--   Definitions and structural lemmas for Mem Iff Conjugate Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
namespace GlobalTheory
structure CMType (E : Type*) [Field E] where

  carrier : Set (E →+* ℂ)

  mem_iff_conjugate_notMem' : ∀ τ, τ ∈ carrier ↔ ComplexEmbedding.conjugate τ ∉ carrier
namespace CMType
section Field
variable {E : Type*} [Field E]
instance : SetLike (CMType E) (E →+* ℂ) where
  coe := carrier
  coe_injective := by
    rintro ⟨a, _⟩ ⟨b, _⟩ h
    congr
instance : PartialOrder (CMType E) := .ofSetLike (CMType E) (E →+* ℂ)
theorem mem_iff_conjugate_notMem (Φ : CMType E) (τ : E →+* ℂ) :
    τ ∈ Φ ↔ ComplexEmbedding.conjugate τ ∉ Φ := Φ.mem_iff_conjugate_notMem' τ
theorem conjugate_mem_iff (Φ : CMType E) (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate τ ∈ Φ ↔ τ ∉ Φ := by
  rw [mem_iff_conjugate_notMem Φ τ, not_not]
theorem mem_or_conjugate_mem (Φ : CMType E) (τ : E →+* ℂ) :
    τ ∈ Φ ∨ ComplexEmbedding.conjugate τ ∈ Φ := by
  rw [conjugate_mem_iff]
  exact em _
def conjugate (Φ : CMType E) : CMType E where
  carrier := {τ | ComplexEmbedding.conjugate τ ∈ Φ}
  mem_iff_conjugate_notMem' _ := Φ.mem_iff_conjugate_notMem _
noncomputable def sumEquiv (Φ : CMType E) : Φ ⊕ Φ ≃ (E →+* ℂ) :=
  Equiv.ofBijective (Sum.elim (fun τ => τ.1) (fun τ => ComplexEmbedding.conjugate τ.1)) <| by
    have hinv : Function.Involutive (ComplexEmbedding.conjugate (K := E)) := star_involutive
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [Subtype.ext h]
      · exact absurd (h ▸ a.2) ((Φ.mem_iff_conjugate_notMem _).mp b.2)
      · exact absurd (h ▸ b.2) ((Φ.mem_iff_conjugate_notMem _).mp a.2)
      · rw [Subtype.ext (hinv.injective h)]
    · intro τ
      rcases Φ.mem_or_conjugate_mem τ with h | h
      · exact ⟨.inl ⟨τ, h⟩, rfl⟩
      · exact ⟨.inr ⟨_, h⟩, hinv τ⟩
noncomputable def ofPlaces (E : Type*) [Field E] [CharZero E] [IsTotallyComplex E] :
    CMType E where
  carrier := Set.range (InfinitePlace.embedding (K := E))
  mem_iff_conjugate_notMem' τ := by
    constructor
    · rintro ⟨w, rfl⟩ ⟨w', h⟩
      have h1 : w' = w := by
        rw [← InfinitePlace.mk_embedding w', h, InfinitePlace.mk_conjugate_eq,
          InfinitePlace.mk_embedding]
      rw [h1] at h
      exact IsTotallyComplex.complexEmbedding_not_isReal w.embedding
        (ComplexEmbedding.isReal_iff.mpr h.symm)
    · intro h
      rcases InfinitePlace.embedding_mk_eq τ with h1 | h1
      · exact ⟨_, h1⟩
      · exact absurd ⟨_, h1⟩ h
instance [CharZero E] [IsTotallyComplex E] : Nonempty (CMType E) := ⟨ofPlaces E⟩
end Field
section NumberField
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)
noncomputable instance : Fintype Φ := Fintype.ofFinite _
theorem two_mul_card : 2 * Fintype.card Φ = Module.finrank ℚ E := by
  rw [← Embeddings.card E ℂ, ← Fintype.card_congr Φ.sumEquiv, Fintype.card_sum, two_mul]
instance : Nonempty Φ := by
  rw [← Fintype.card_pos_iff]
  have h := Φ.two_mul_card
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega
end NumberField
example {E : Type*} [Field E] [NumberField E] (Φ : CMType E) : Φ.conjugate ≠ Φ := by
  intro h
  obtain ⟨τ⟩ : Nonempty Φ := inferInstance
  have h1 : τ.1 ∈ Φ.conjugate := by rw [h]; exact τ.2
  exact (Φ.mem_iff_conjugate_notMem _).mp τ.2 h1
end CMType
end GlobalTheory


