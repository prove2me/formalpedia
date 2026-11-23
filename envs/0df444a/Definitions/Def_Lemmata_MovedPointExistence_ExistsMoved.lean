-- Prove2me | Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
-- name    : Lemmata_MovedPointExistence_ExistsMoved
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:45.342987+00:00
-- url     : https://prove2.me/theorems/9c662bbc-54b5-4731-9b87-5d1b024c1a82
-- title:
--   Exists Moved
-- statement:
--   Definitions and structural lemmas for Exists Moved, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MovedPointExistence/ExistsMoved.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open NormedSpace
namespace Bl.MovedPointExistence
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Bl.MovedPointExistence


