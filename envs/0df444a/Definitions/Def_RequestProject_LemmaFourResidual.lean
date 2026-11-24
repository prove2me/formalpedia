-- Prove2me | Definitions.Def_RequestProject_LemmaFourResidual
-- name    : RequestProject_LemmaFourResidual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:18:02.343949+00:00
-- url     : https://prove2.me/theorems/583cb864-cf62-4d3a-b44d-874d965fa24d
-- title:
--   Lemma Four Residual
-- statement:
--   Definitions and structural lemmas for Lemma Four Residual, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
end FairSelling


