-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJointDef
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePKeyJointDef
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:38.974715+00:00
-- url     : https://prove2.me/theorems/83102114-4ac7-4917-9b2f-340bb8c2431e
-- title:
--   Row Tie PKey Joint Def
-- statement:
--   Definitions and structural lemmas for Row Tie PKey Joint Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePKeyJointDef.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
namespace RowTiePKey
def JointEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C], IsAlgClosed C → ∀ (n q : ℕ), 2 ≤ q →
    ∀ (T : Set (Matrix (Fin n) (Fin n) C)), (∀ t ∈ T, t ^ q = t) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
    ∀ v : Fin n → C, ∃ (m : ℕ) (w : Fin m → Fin n → C), v = ∑ j, w j ∧
      ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j
end RowTiePKey
end Formalism.L2.FormalSeriesBounds


