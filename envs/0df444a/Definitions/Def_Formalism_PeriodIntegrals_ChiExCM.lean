-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
-- name    : Formalism_PeriodIntegrals_ChiExCM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:58.191794+00:00
-- url     : https://prove2.me/theorems/47847c0c-a078-4bbe-a920-cdd59b7aba04
-- title:
--   Chi Ex CM
-- statement:
--   Definitions and structural lemmas for Chi Ex CM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ChiExCM.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open NumberField
def ChiExCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    ∀ (S : Type) [Fintype S] (emb : S → E →+* ℂ), (∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ s, emb s x = 1) →
    ∃ χ : Submodule (𝓞 E) E → ℂ,
      (∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∃ 𝔞' : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔞' ↔ c x ∈ 𝔞) ∧ 𝔞 * 𝔞' = 1) →
        (∃ 𝔟' : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟' ↔ c x ∈ 𝔟) ∧ 𝔟 * 𝔟' = 1) → χ (𝔞 * 𝔟) = χ 𝔞 * χ 𝔟) ∧
      ∀ z : E, z * c z = 1 → χ (Submodule.span (𝓞 E) {z}) = ∏ s, (emb s z)⁻¹
end PI


