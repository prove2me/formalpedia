-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
-- name    : Formalism_PeriodIntegrals_DetIdPG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:38.258097+00:00
-- url     : https://prove2.me/theorems/d862229c-f998-4d34-a6f3-a8f27bae8bc4
-- title:
--   Det Id PG
-- statement:
--   Definitions and structural lemmas for Det Id PG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DetIdPG.lean

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
namespace PI
namespace DetIdPG
def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i
def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range
end DetIdPG
def DetIdPG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (L L₀ : Submodule (𝓞 E) (Fin N → E)), DetIdPG.IsSDLat E N L → DetIdPG.IsSDLat E N L₀ →
    (∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, (s : E) • x ∈ L₀) ∧ ∀ x ∈ L₀, (s : E) • x ∈ L) →
    ∃ (h : ℕ) (z : E), 0 < h ∧ star z * z = 1 ∧ z * star z = 1 ∧ (∀ ψ : E →+* ℂ_[p], ‖ψ z‖ = 1) ∧
      (Submodule.span (𝓞 E) {x : E | ∃ A : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₀, A.mulVec v ∈ L) ∧ x = A.det}) ^ h =
        Submodule.span (𝓞 E) {z}
end PI


