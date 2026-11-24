-- Prove2me | Definitions.Def_RequestProject_PreliminaryPhase
-- name    : RequestProject_PreliminaryPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:19:15.252666+00:00
-- url     : https://prove2.me/theorems/32b64465-699b-43f6-b530-3cd05ce27f71
-- title:
--   Preliminary Phase
-- statement:
--   Definitions and structural lemmas for Preliminary Phase, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
end FairSelling


