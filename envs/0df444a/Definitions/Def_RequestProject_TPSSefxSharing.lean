-- Prove2me | Definitions.Def_RequestProject_TPSSefxSharing
-- name    : RequestProject_TPSSefxSharing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:12:04.172199+00:00
-- url     : https://prove2.me/theorems/08cc8620-b85d-42ae-86d1-1b2055bb61ad
-- title:
--   TPSSefx Sharing
-- statement:
--   Definitions and structural lemmas for TPSSefx Sharing, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace SharedProceeds
noncomputable def sv : Fin 4 → ℝ := fun g => if g = 0 then 10 else 1
noncomputable def sp : Fin 4 → ℝ := fun g => if g = 0 then 10 else 0
end SharedProceeds
end FairSelling


