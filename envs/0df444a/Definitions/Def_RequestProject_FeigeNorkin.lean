-- Prove2me | Definitions.Def_RequestProject_FeigeNorkin
-- name    : RequestProject_FeigeNorkin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:09:20.472833+00:00
-- url     : https://prove2.me/theorems/324cd90d-0a63-4b1d-ac8e-d87a1587796b
-- title:
--   Feige Norkin
-- statement:
--   Definitions and structural lemmas for Feige Norkin, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace FeigeNorkin
def fnR : Fin 8 → ℕ := ![18, 18, 30, 3, 3, 12, 12, 12]
def fnC : Fin 8 → ℕ := ![22, 20, 25, 3, 5, 11, 11, 11]
def fnU : Fin 8 → ℕ := ![22, 22, 31, 0, 0, 11, 11, 11]
def fnW : Fin 3 → Fin 8 → ℕ := ![fnR, fnC, fnU]
def valOf (w : Fin 8 → ℕ) (i : Fin 3) (a b c d e f g h : Fin 3) : ℕ :=
  (if a = i then w 0 else 0) + (if b = i then w 1 else 0) + (if c = i then w 2 else 0) +
  (if d = i then w 3 else 0) + (if e = i then w 4 else 0) + (if f = i then w 5 else 0) +
  (if g = i then w 6 else 0) + (if h = i then w 7 else 0)
end FeigeNorkin
end FairSelling


