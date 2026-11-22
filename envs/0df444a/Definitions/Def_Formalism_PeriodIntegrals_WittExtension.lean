-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WittExtension
-- name    : Formalism_PeriodIntegrals_WittExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:11.787975+00:00
-- url     : https://prove2.me/theorems/30cb522c-5dd1-4971-ad84-96fda002e6a2
-- title:
--   Witt Extension
-- statement:
--   Definitions and structural lemmas for Witt Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WittExtension.lean

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
def WittExtension : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, star (B x y) = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) →
    ∀ (U : Submodule K V) (f : U →ₗ[K] V), Function.Injective f →
      (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x
end PI


