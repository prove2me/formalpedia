-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_RankTruncation_LocalAdditiveCharacterExpansion
-- name    : Formalism_SharpRestriction_Divisibility_RankTruncation_LocalAdditiveCharacterExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:47.373045+00:00
-- url     : https://prove2.me/theorems/342b9cd0-c215-4409-b3a4-da143d6c9c31
-- title:
--   Local Additive Character Expansion
-- statement:
--   Definitions and structural lemmas for Local Additive Character Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/RankTruncation/LocalAdditiveCharacterExpansion.lean

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
namespace ConditionalKappaBounds.L2
def LocalAdditiveCharacterExpansion : Prop := ∀ (p : ℕ) [Fact p.Prime] (f n : ℕ) (R : Type) [CommRing R] [IsDomain R] (ζ : R),
  IsPrimitiveRoot ζ p →
  ∀ φ : (Fin f × Fin n → ℚ_[p]) → R,
    (∀ x, φ x ≠ 0 → ∀ a, ‖x a‖ ≤ 1) →
    (∀ (x : Fin f × Fin n → ℚ_[p]) (z : Fin f × Fin n → ℤ_[p]),
      φ (fun a => x a + (p : ℚ_[p]) * (z a : ℚ_[p])) = φ x) →
    ∃ c : (Fin f × Fin n → ZMod p) → R, ∀ x : Fin f × Fin n → ℚ_[p],
      (p : R) ^ (f * n) * φ x =
        open Classical in
        if h : ∀ a, ‖x a‖ ≤ 1 then
          ∑ y : Fin f × Fin n → ZMod p,
            c y * ζ ^ (∑ a, PadicInt.toZMod (⟨x a, h a⟩ : ℤ_[p]) * y a).val
        else 0
end ConditionalKappaBounds.L2


