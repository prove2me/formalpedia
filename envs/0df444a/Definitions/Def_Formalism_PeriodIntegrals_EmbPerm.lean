-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_EmbPerm
-- name    : Formalism_PeriodIntegrals_EmbPerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:16.854581+00:00
-- url     : https://prove2.me/theorems/a1d5d5ee-700e-46d3-8858-51dad03c4a46
-- title:
--   Emb Perm
-- statement:
--   Definitions and structural lemmas for Emb Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/EmbPerm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Classical
def EmbPermDefs.liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0
def EmbPermDefs.cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (EmbPermDefs.liftM M x)
def EmbPerm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
      (∀ a : K, φ₀ (a : E) ∈ M ∧ EmbPermDefs.cj M ρ (φ₀ (a : E)) = φ₀ (a : E)) → (∀ s x, emb s x ∈ M) →
      ∃ π : Equiv.Perm S, ∀ s x, EmbPermDefs.cj M ρ (emb s x) = emb (π s) x
end PI


