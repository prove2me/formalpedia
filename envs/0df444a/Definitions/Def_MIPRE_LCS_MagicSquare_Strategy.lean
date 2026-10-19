-- Prove2me | Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
-- name    : MIPRE_LCS_MagicSquare_Strategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:35.909402+00:00
-- url     : https://prove2.me/theorems/63d16c84-57e5-40ae-a416-e0ecd5f0cc7e
-- title:
--   Definitions of Strategy: Mermin-Peres Magic Square Game Strategy This module defines the layout for the Mermin-Peres magic square Linear…
-- statement:
--   The definitions of the module `MIPRE.LCS.MagicSquare.Strategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mermin-Peres Magic Square Game Strategy. This module defines the layout for the Mermin-Peres magic square Linear Constraint System (LCS) game and provides a valid quantum strategy for it using observables. It verifies the commutativity requirements (both local within equations and global bipartite commutativity) necessary to define a valid `ObservableStrategy`.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   **Definitions** (2): `MIPRE.LCS.MagicSquare.game` (The support-style magic square game, with the final column equation having odd parity.); `MIPRE.LCS.MagicSquare.layout` (The layout of the Mermin-Peres magic square game.).
--
--   **Formalization Note** The bundle is the module `MIPRE.LCS.MagicSquare.Strategy` (`MIPRE/LCS/MagicSquare/Strategy.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/MagicSquare/Strategy.lean; blueprint def:magic-square

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/MagicSquare/Strategy.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Pauli

/-!
# Mermin-Peres Magic Square Game Strategy

This module defines the layout for the Mermin-Peres magic square Linear Constraint System (LCS) game
and provides a valid quantum strategy for it using observables.

It verifies the commutativity requirements
(both local within equations and global bipartite commutativity)
necessary to define a valid `ObservableStrategy`.
-/

namespace MIPRE.LCS.MagicSquare

section Layout
/-! ## Layout
This section defines the layout/geometry of the Mermin-Peres magic square game.
  -/
/-- The layout of the Mermin-Peres magic square game.
It consists of 6 equations (3 rows and 3 columns) over 9 variables (the cells of the 3x3 grid). -/
def layout : Layout  := {
  r := 6
  s := 9
  V := fun i ↦
  match i with
  | 0 => {0, 1, 2}
  | 1 => {3, 4, 5}
  | 2 => {6, 7, 8}
  | 3 => {0, 3, 6}
  | 4 => {1, 4, 7}
  | 5 => {2, 5, 8}
  }

end Layout

/-- The support-style magic square game, with the final column equation having odd parity. -/
def game : Game layout := {
  b := fun i ↦ if i = ⟨5, by decide⟩ then 1 else 0
}

open Matrix
open scoped Kronecker
open Pauli

section Grid
/-! ## Grid
This section defines a strategy for the game from the previous section,
given as a grid of observables.
-/

end Grid

section Commutativity
/-!
## Commutativity
This section proves the commutativity properties of the magic square grid.

These properties are required for the strategy to be valid.
-/

end Commutativity

section Strategy
/-!
## Strategy
This section shows that the grid strategy is a valid strategy for the magic square game.
-/

end Strategy

end MIPRE.LCS.MagicSquare


