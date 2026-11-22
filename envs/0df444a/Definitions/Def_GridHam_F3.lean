-- Prove2me | Definitions.Def_GridHam_F3
-- name    : GridHam_F3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:27:04.29142+00:00
-- url     : https://prove2.me/theorems/33b4e2b0-28d7-471b-83b8-34ad8a5f9605
-- title:
--   F3
-- statement:
--   Definitions and structural lemmas for F3, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean

module
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
def PNext (p : List Coord) (x y : Coord) : Prop := ∃ l1 l2, p = l1 ++ x :: y :: l2
def shiftL2 (v : Coord) : Coord := (v.1 - 2, v.2)
end GridHam


