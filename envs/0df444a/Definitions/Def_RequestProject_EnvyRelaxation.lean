-- Prove2me | Definitions.Def_RequestProject_EnvyRelaxation
-- name    : RequestProject_EnvyRelaxation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:11:30.388979+00:00
-- url     : https://prove2.me/theorems/8f1c6017-b420-4e56-a074-ec87ba499f46
-- title:
--   Envy Relaxation
-- statement:
--   Definitions and structural lemmas for Envy Relaxation, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EnvyRelaxation.lean

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace RelaxEx
def p : Fin 2 → ℝ := ![1, 1]
def v : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![0, 0]]
def o : Outcome (Fin 2) 2 := ⟨{1}, ![∅, {0}], ![1, 0]⟩
end RelaxEx
end FairSelling


