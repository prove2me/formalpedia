-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:07:28.636419+00:00
-- url     : https://prove2.me/theorems/cd9e99b3-2793-4667-8132-7bacf8ff689d
-- title:
--   Row Tie PSplit LA
-- statement:
--   Definitions and structural lemmas for Row Tie PSplit LA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
namespace RowTiePSplit
open Polynomial Matrix
section Sep
variable {K : Type} [Field K] [CharZero K]
end Sep
section Mat
variable {K : Type} [Field K] {n : ℕ}
end Mat
end RowTiePSplit
end Formalism.L2.FormalSeriesBounds


