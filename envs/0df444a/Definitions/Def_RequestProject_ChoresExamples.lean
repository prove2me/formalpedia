-- Prove2me | Definitions.Def_RequestProject_ChoresExamples
-- name    : RequestProject_ChoresExamples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:10.206649+00:00
-- url     : https://prove2.me/theorems/439f9af9-8f38-4d68-9826-33aba727a356
-- title:
--   Chores Examples
-- statement:
--   Definitions and structural lemmas for Chores Examples, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
namespace ExpensiveChore
def cc : Fin 1 → ℝ := fun _ => 10
def pp : Fin 1 → ℝ := fun _ => 6
def oo : Outcome (Fin 1) 3 :=
  { outsourced := Finset.univ
    kept := fun _ => ∅
    pay := fun _ => 2 }
end ExpensiveChore
end FairChores


