-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:59.91444+00:00
-- url     : https://prove2.me/theorems/50545eb7-bee1-4d0c-a8da-c4a36dda4cd9
-- title:
--   PRename Int Num
-- statement:
--   Definitions and structural lemmas for PRename Int Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace RenameIntNum
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)
def precompIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      simpa using h (e.symm k)
    · intro h k
      exact h (e k)
end RenameIntNum
end
end GroundTheory.Heights₂.Heights.FieldNumbers


