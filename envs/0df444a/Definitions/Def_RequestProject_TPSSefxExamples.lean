-- Prove2me | Definitions.Def_RequestProject_TPSSefxExamples
-- name    : RequestProject_TPSSefxExamples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:11:20.437433+00:00
-- url     : https://prove2.me/theorems/357ff5ac-69f2-4beb-ab48-9703b8d92874
-- title:
--   TPSSefx Examples
-- statement:
--   Definitions and structural lemmas for TPSSefx Examples, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxExamples.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace TPSSefxCounterexample
abbrev Gd := Fin 4
def exv : Gd → ℝ := ![0, 18, 19, 5]
def exp : Gd → ℝ := ![18, 0, 0, 0]
def exV : Fin 2 → Gd → ℝ := fun _ => exv
def exOutcome : Outcome Gd 2 where
  sold := {0}
  kept := ![{1}, {2, 3}]
  money := ![18, 0]
def exGoodOutcome : Outcome Gd 2 where
  sold := {0}
  kept := ![{1}, {2, 3}]
  money := ![12, 6]
end TPSSefxCounterexample
end FairSelling


