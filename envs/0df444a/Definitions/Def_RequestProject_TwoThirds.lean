-- Prove2me | Definitions.Def_RequestProject_TwoThirds
-- name    : RequestProject_TwoThirds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:18:28.370084+00:00
-- url     : https://prove2.me/theorems/ddb1e014-ea40-4abc-9cc7-5ddad59a8fb3
-- title:
--   Two Thirds
-- statement:
--   Definitions and structural lemmas for Two Thirds, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
end FairSelling


