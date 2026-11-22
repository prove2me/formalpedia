-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
-- name    : Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:54.176267+00:00
-- url     : https://prove2.me/theorems/9780cddc-6972-4664-b675-0d8b27a8439a
-- title:
--   Lat Sum
-- statement:
--   Definitions and structural lemmas for Lat Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.P
open Finset
noncomputable def psi (n : ℤ) : ℝ := (4 / (|(n : ℝ)| + 1)) ^ (5 / 4 : ℝ)
end Formalism.NuclearRankWeightBounds.P


