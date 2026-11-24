-- Prove2me | Definitions.Def_RequestProject_CanonicalStrict
-- name    : RequestProject_CanonicalStrict
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:16:43.690829+00:00
-- url     : https://prove2.me/theorems/154bdd82-5fc7-4599-a12d-5b467dc890c7
-- title:
--   Canonical Strict
-- statement:
--   Definitions and structural lemmas for Canonical Strict, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
end FairSelling


