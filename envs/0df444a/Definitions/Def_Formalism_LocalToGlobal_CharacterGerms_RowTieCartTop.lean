-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartTop
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieCartTop
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:53.108021+00:00
-- url     : https://prove2.me/theorems/845eb91b-c1d6-4a23-a153-d78c94b466a3
-- title:
--   Row Tie Cart Top
-- statement:
--   Definitions and structural lemmas for Row Tie Cart Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartTop.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
def GermIAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), GermISt Y
end Formalism.L2.FormalSeriesBounds


