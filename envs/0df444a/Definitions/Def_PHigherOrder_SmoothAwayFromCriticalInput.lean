-- Prove2me | Definitions.Def_PHigherOrder_SmoothAwayFromCriticalInput
-- name    : PHigherOrder_SmoothAwayFromCriticalInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:14:01.606797+00:00
-- url     : https://prove2.me/theorems/81e290b4-800c-4fb2-ad06-e97fc5b3bc45
-- title:
--   Smooth Away From Critical Input
-- statement:
--   Definitions and structural lemmas for Smooth Away From Critical Input, from na0b and contributors's pinned Higher-order estimates for planar p-harmonic functions under the stated hypotheses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/SmoothAwayFromCriticalInput.lean

import Definitions.Def_PHigherOrder_IsPHarm
set_option autoImplicit false
structure SmoothAwayFromCriticalInput (p : ℝ) : Prop where
  smooth : ∀ (Ω : Set Plane) (u : Plane → ℝ) (g : Plane → Plane),
      IsPHarm p Ω u g → ∀ U : Set Plane, IsOpen U → U ⊆ Ω →
      ContDiffOn ℝ 1 u U → (∀ x ∈ U, gradient u x ≠ 0) →
      ContDiffOn ℝ (⊤ : ℕ∞) u U


