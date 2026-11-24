-- Prove2me | Definitions.Def_RequestProject_Examples
-- name    : RequestProject_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:18:20.204041+00:00
-- url     : https://prove2.me/theorems/a48caf98-a357-4de5-8d0b-fb055fb05ce6
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Examples.lean

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace Examples
def vsell : Fin 1 → ℝ := ![0]
def psell : Fin 1 → ℝ := ![2]
def vex : Fin 2 → ℝ := ![3, 1]
def pex : Fin 2 → ℝ := ![0, 0]
end Examples
end FairSelling


