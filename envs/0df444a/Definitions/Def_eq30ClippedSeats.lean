-- Prove2me | Definitions.Def_eq30ClippedSeats
-- name    : eq30ClippedSeats
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T01:08:02.975042+00:00
-- url     : https://prove2.me/theorems/0295c56d-750e-43cd-9e42-28d528a20b8e
-- title:
--   eq30ClippedSeats
-- statement:
--   Automatically extracted helper definition eq30ClippedSeats from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

/-- Seats allocated to the newly added class, clipped to its capacity. -/
def eq30ClippedSeats (p x s : ℝ) : ℝ := min x (max 0 (s - p))


