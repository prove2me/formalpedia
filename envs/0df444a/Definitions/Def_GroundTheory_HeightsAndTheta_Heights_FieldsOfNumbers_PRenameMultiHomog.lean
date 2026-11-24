-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:01.701435+00:00
-- url     : https://prove2.me/theorems/b07efcd3-ec12-48a7-a79d-c97afcb5d9e0
-- title:
--   PRename Multi Homog
-- statement:
--   Definitions and structural lemmas for PRename Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
def extendAddHom {K K' : Type} (j : K ↪ K') : (K → ℕ) →+ (K' → ℕ) where
  toFun x := Function.extend j x 0
  map_zero' := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_add' x y := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
end
end GroundTheory.Heights₂.Heights.FieldNumbers


