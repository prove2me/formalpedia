-- Prove2me | Definitions.Def_RequestProject_TPSSefxMixedExample
-- name    : RequestProject_TPSSefxMixedExample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:23:41.501874+00:00
-- url     : https://prove2.me/theorems/f5c742ab-7a6b-4040-beba-377bb28d7f0b
-- title:
--   TPSSefx Mixed Example
-- statement:
--   Definitions and structural lemmas for TPSSefx Mixed Example, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace MixedGood
noncomputable def mp : Fin 3 → ℝ := ![4, 0, 0]
noncomputable def mv : Fin 2 → Fin 3 → ℝ := ![![0, 0, 0], ![100, 6, 6]]
end MixedGood
end FairSelling


