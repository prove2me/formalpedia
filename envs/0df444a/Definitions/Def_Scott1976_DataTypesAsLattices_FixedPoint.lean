-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
-- name    : Scott1976_DataTypesAsLattices_FixedPoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:23.876964+00:00
-- url     : https://prove2.me/theorems/a8612a92-2ed0-5b3f-86a1-28172986534e
-- title:
--   Fixed Point
-- statement:
--   Definitions and structural lemmas for Fixed Point, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)
def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n
end Scott1976.DataTypesAsLattices


