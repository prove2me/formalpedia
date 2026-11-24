-- Prove2me | Definitions.Def_RequestProject_FeigeNorkinChores
-- name    : RequestProject_FeigeNorkinChores
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:15.949088+00:00
-- url     : https://prove2.me/theorems/4764c0cd-cac6-49e1-9f45-b2ed430c433c
-- title:
--   Feige Norkin Chores
-- statement:
--   Definitions and structural lemmas for Feige Norkin Chores, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace FairChores
namespace FeigeNorkinChores
def fcR : Fin 8 → ℕ := ![180, 180, 240, 60, 60, 80, 140, 140]
def fcC : Fin 8 → ℕ := ![170, 150, 255, 65, 60, 105, 125, 150]
def fcU : Fin 8 → ℕ := ![152, 152, 228, 92, 76, 76, 152, 152]
def fcW : Fin 3 → Fin 8 → ℕ := ![fcR, fcC, fcU]
def costOf (w : Fin 8 → ℕ) (i : Fin 3) (a b c d e f g h : Fin 3) : ℕ :=
  (if a = i then w 0 else 0) + (if b = i then w 1 else 0) + (if c = i then w 2 else 0) +
  (if d = i then w 3 else 0) + (if e = i then w 4 else 0) + (if f = i then w 5 else 0) +
  (if g = i then w 6 else 0) + (if h = i then w 7 else 0)
end FeigeNorkinChores
end FairChores


