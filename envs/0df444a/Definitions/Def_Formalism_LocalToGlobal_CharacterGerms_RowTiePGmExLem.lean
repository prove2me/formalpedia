-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:03.466497+00:00
-- url     : https://prove2.me/theorems/34e7509d-4ff0-4151-969b-5a8894c8eec1
-- title:
--   Row Tie PGm Ex Lem
-- statement:
--   Definitions and structural lemmas for Row Tie PGm Ex Lem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
def Kf (ε : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) / ε⌉₊
def Cpl (V : VF C) : Prop :=
  ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)
end Formalism.L2.FormalSeriesBounds.GmExArith


