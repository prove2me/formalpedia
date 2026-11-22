-- Prove2me | Definitions.Def_GridHam_Main
-- name    : GridHam_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:34:43.342444+00:00
-- url     : https://prove2.me/theorems/bf6a149f-55bb-4f95-9566-3d755a38c867
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Main.lean

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
def SuffP (n : ℕ) : Prop :=
  ∀ (w h : ℕ) (s t : Coord), w + h ≤ n → InBounds w h s → InBounds w h t → s ≠ t →
    IsAcceptable w h s t → HasHamPath w h s t
end GridHam


