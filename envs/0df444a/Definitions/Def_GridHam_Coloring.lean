-- Prove2me | Definitions.Def_GridHam_Coloring
-- name    : GridHam_Coloring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:22:22.78899+00:00
-- url     : https://prove2.me/theorems/58144746-1cca-4231-8d1e-e5faeeba48cb
-- title:
--   Coloring
-- statement:
--   Definitions and structural lemmas for Coloring, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Coloring.lean

module
public import Definitions.Def_GridHam_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
def cnt1 (l : List Coord) : ℕ := l.countP (fun v => decide (parity v = 1))
end GridHam


