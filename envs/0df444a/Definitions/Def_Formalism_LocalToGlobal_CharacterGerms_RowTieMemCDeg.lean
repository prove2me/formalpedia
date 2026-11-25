-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:43.077446+00:00
-- url     : https://prove2.me/theorems/3055b9ee-5803-4cd2-aebd-72cc679130e4
-- title:
--   Row Tie Mem CDeg
-- statement:
--   Definitions and structural lemmas for Row Tie Mem CDeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCDeg.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
end Formalism.L2.FormalSeriesBounds.RF


