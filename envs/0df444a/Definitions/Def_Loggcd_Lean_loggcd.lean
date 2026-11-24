-- Prove2me | Definitions.Def_Loggcd_Lean_loggcd
-- name    : Loggcd_Lean_loggcd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T13:58:26.886689+00:00
-- url     : https://prove2.me/theorems/18bc388f-5ffa-4902-8a9d-fab8497c3816
-- title:
--   loggcd
-- statement:
--   Definitions and structural lemmas for loggcd, from irregular-rhomboid (irregular-rhomboid/log-gcd-lean; see pinned CC0-1.0 LICENSE)'s pinned Positive semidefiniteness of the log-gcd kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/irregular-rhomboid/log-gcd-lean/blob/170787f66795b7d732a29922244638df9ec737da/Loggcd/Lean/loggcd.lean

import Mathlib
set_option autoImplicit true
open Finset ArithmeticFunction
variable {ι : Type*} [Fintype ι]


