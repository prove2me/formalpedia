-- Prove2me | Definitions.Def_RequestProject_ConfigSplit
-- name    : RequestProject_ConfigSplit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:16:03.036518+00:00
-- url     : https://prove2.me/theorems/827fd5ef-161e-4e16-87b3-276ab2cc0729
-- title:
--   Config Split
-- statement:
--   Definitions and structural lemmas for Config Split, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
end FairSelling


