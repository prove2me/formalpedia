-- Prove2me | Definitions.Def_RequestProject_ChoresMMSApprox
-- name    : RequestProject_ChoresMMSApprox
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:29:45.555908+00:00
-- url     : https://prove2.me/theorems/e15a56ce-5183-483b-b459-5a4b1cfecd70
-- title:
--   Chores MMSApprox
-- statement:
--   Definitions and structural lemmas for Chores MMSApprox, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSApprox.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresBagFilling
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
end FairChores


