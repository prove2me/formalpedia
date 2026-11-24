-- Prove2me | Definitions.Def_RequestProject_ThreeAgentCash
-- name    : RequestProject_ThreeAgentCash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:13:22.161948+00:00
-- url     : https://prove2.me/theorems/48be113f-d750-4a80-a64c-33e7ff7415a5
-- title:
--   Three Agent Cash
-- statement:
--   Definitions and structural lemmas for Three Agent Cash, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCash.lean

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def cashVal (R : Finset G) (w : G → ℝ) : Option G → ℝ
  | none => 0
  | some g => restrictVal R w g
def cashPrice (R : Finset G) (p : G → ℝ) (c : ℝ) : Option G → ℝ
  | none => c
  | some g => restrictVal R p g
end FairSelling


