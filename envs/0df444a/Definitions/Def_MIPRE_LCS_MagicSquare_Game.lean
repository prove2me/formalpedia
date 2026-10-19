-- Prove2me | Definitions.Def_MIPRE_LCS_MagicSquare_Game
-- name    : MIPRE_LCS_MagicSquare_Game
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:26.8918+00:00
-- url     : https://prove2.me/theorems/07e6c8c0-4e8c-4f9d-9c5d-5194bcfbc527
-- title:
--   Definitions of Game: The Magic Square as a nonlocal game `MIPRE.LCS.MagicSquare.game` is the Mermin--Peres magic square as an LCS instance;…
-- statement:
--   The definitions of the module `MIPRE.LCS.MagicSquare.Game` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Magic Square as a nonlocal game. `MIPRE.LCS.MagicSquare.game` is the Mermin--Peres magic square as an LCS instance; `nonlocalGame` is the two-player game it induces through `MIPRE.LCS.Game.toNonlocalGame`, which is what blueprint `lem:ms-direct-anticomm` and the Pauli basis test's Magic Square subtest are about. The point of this file is the **non-vacuity witnesses**. A decider that accepts everything, or rejects everything, makes every soundness statement about the game either false or empty, and that is not a hypothetical: `reports/clgame-format-check-missing.md` records the seeded CL…
--
--   **Definitions** (5): `MIPRE.LCS.MagicSquare.cell` (The `j`-th cell of constraint `c`.); `MIPRE.LCS.MagicSquare.cellIdx` (The position of the variable `j` within the support of constraint `c`, the inverse of `cell c`; junk (`2`) for a variable outside the…); `MIPRE.LCS.MagicSquare.cellNat` (The index of the `j`-th cell of the `c`-th equation.); `MIPRE.LCS.MagicSquare.nonlocalGame` (**The Magic Square as a nonlocal game.**); `MIPRE.LCS.MagicSquare.v` (A variable index, written as a numeral.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `V_nonempty`, `cellIdx_cell`, `r_pos`.
--
--   **Formalization Note** The bundle is the module `MIPRE.LCS.MagicSquare.Game` (`MIPRE/LCS/MagicSquare/Game.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 15 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/MagicSquare/Game.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/MagicSquare/Game.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy

/-!
# The Magic Square as a nonlocal game

`MIPRE.LCS.MagicSquare.game` is the Mermin--Peres magic square as an LCS instance;
`nonlocalGame` is the two-player game it induces through `MIPRE.LCS.Game.toNonlocalGame`, which
is what blueprint `lem:ms-direct-anticomm` and the Pauli basis test's Magic Square subtest are
about.

The point of this file is the **non-vacuity witnesses**. A decider that accepts everything, or
rejects everything, makes every soundness statement about the game either false or empty, and
that is not a hypothetical: `reports/clgame-format-check-missing.md` records the seeded CL
game's missing format check doing exactly that. So each of the four possibilities is pinned
here by `decide` on explicit answers:

* an oriented pair that is **accepted** (`accepts_zero`), in both orientations;
* one that is **rejected because the bits disagree** (`rejects_disagree`);
* one that is **rejected because the assignment violates its equation**
  (`rejects_unsatisfied`) --- note this one has the bits *agreeing*, so it isolates the
  parity check;
* one that is **rejected because an answer has the wrong shape** (`rejects_shape`).

`layout.V 5 = {2, 5, 8}` carries the odd right-hand side, so `rejects_odd_column` also checks
that the parity actually reads `game.b` rather than always testing against zero.
-/

namespace MIPRE.LCS.MagicSquare

open MIPRE.LCS

/-- The magic square has six equations. -/
theorem r_pos : 0 < layout.r := by decide

/-- Every equation of the magic square has a nonempty support. -/
theorem V_nonempty : ∀ i, (layout.V i).Nonempty := by decide

/-- **The Magic Square as a nonlocal game.** -/
noncomputable def nonlocalGame : MIPRE.Game layout.Question layout.Question
    layout.Answer layout.Answer :=
  game.toNonlocalGame r_pos V_nonempty

/-! ## Non-vacuity

The all-zero assignment satisfies equation `0` (whose right-hand side is `0`), so with the
matching bit it is accepted; changing the bit, or the assignment's parity, is rejected. -/

/-- A variable index, written as a numeral. `layout.s` is not a literal, so the `OfNat`
instance does not fire. -/
def v (k : ℕ) (h : k < layout.s := by decide) : Fin layout.s := ⟨k, h⟩

/-! ## The cells of a constraint

The magic square's six equations are the three rows and the three columns, in that order, so
the `j`-th cell of equation `c` is `3c + j` for a row and `3j + (c - 3)` for a column. -/

/-- The index of the `j`-th cell of the `c`-th equation. -/
def cellNat (c j : ℕ) : ℕ := if c < 3 then 3 * c + j else 3 * j + (c - 3)

/-- The `j`-th cell of constraint `c`. -/
def cell (c : Fin layout.r) (j : Fin 3) : Fin layout.s :=
  ⟨cellNat c.val j.val, by
    have hc := c.isLt
    have hj := j.isLt
    simp only [layout] at hc ⊢
    simp only [cellNat]
    split_ifs <;> omega⟩

/-- The position of the variable `j` within the support of constraint `c`, the inverse of
`cell c`; junk (`2`) for a variable outside the support. -/
def cellIdx (c : Fin layout.r) (j : Fin layout.s) : Fin 3 :=
  if cell c 0 = j then 0 else if cell c 1 = j then 1 else 2

@[simp] theorem cellIdx_cell (c : Fin layout.r) (k : Fin 3) : cellIdx c (cell c k) = k := by
  revert k; revert c; decide

end MIPRE.LCS.MagicSquare


