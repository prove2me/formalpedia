-- Prove2me | Definitions.Def_ShiQMACenteredGapGeneralSchedule
-- name    : ShiQMACenteredGapGeneralSchedule
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-01T23:37:04.622594+00:00
-- url     : https://prove2.me/theorems/0d7c80f5-8192-4ba0-b1d9-cd20a74605d1
-- title:
--   General-gap QMA bias-normalization and error-reduction schedule
-- statement:
--   Defines the normalization round count and full general-gap round count from the constructive logarithmic schedule.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L31-L37

import Mathlib.Tactic
import Definitions.Def_ShiQMACenteredGap
import Definitions.Def_ShiQMAConstructiveSchedule

set_option autoImplicit false

namespace ShiQMACenteredGap
open ShiQMAConstructiveSchedule

def normalizationRounds (q : Polynomial ℕ) (n : Nat) : Nat :=
  3 * rounds q n
def generalGapRounds (q p : Polynomial ℕ) (n : Nat) : Nat :=
  normalizationRounds q n + rounds p n

end ShiQMACenteredGap


