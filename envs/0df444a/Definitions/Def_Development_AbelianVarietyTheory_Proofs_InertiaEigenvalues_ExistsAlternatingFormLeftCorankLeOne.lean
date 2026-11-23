-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:15.964456+00:00
-- url     : https://prove2.me/theorems/c8fee6ab-f6cc-453f-8a37-3d6c3be8f3b6
-- title:
--   Exists Alternating Form Left Corank Le One
-- statement:
--   Definitions and structural lemmas for Exists Alternating Form Left Corank Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def Good (S₁ S₂ : Submodule K V) : Prop :=
  ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
    (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x
end GlobalTheory.AltCorank


