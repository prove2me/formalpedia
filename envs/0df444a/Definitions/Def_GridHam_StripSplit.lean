-- Prove2me | Definitions.Def_GridHam_StripSplit
-- name    : GridHam_StripSplit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:24:50.809802+00:00
-- url     : https://prove2.me/theorems/2e539c4a-5fa5-45d9-abb5-ae23a9727c2a
-- title:
--   Strip Split
-- statement:
--   Definitions and structural lemmas for Strip Split, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean

module
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
def shiftX (d : ℕ) (v : Coord) : Coord := (v.1 + d, v.2)
def swapXY (v : Coord) : Coord := (v.2, v.1)
def colSeg (c lo : ℕ) : ℕ → List Coord
  | 0 => [(c, lo)]
  | k + 1 => (c, lo + (k + 1)) :: colSeg c lo k
def rightDetour (w h y : ℕ) : List Coord :=
  colSeg w 0 y ++ ((colSeg (w + 1) 0 (h - 1)).reverse ++ colSeg w (y + 1) (h - 1 - (y + 1)))
def reflectX (w : ℕ) (v : Coord) : Coord := (w - 1 - v.1, v.2)
end GridHam


