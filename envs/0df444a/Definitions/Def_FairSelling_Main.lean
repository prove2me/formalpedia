-- Prove2me | Definitions.Def_FairSelling_Main
-- name    : FairSelling_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:21.736799+00:00
-- url     : https://prove2.me/theorems/0ad8042d-c03e-4869-a243-bb5579d0549c
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/Main.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option grind.warning false


