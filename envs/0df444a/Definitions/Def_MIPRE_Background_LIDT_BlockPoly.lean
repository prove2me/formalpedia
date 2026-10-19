-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_BlockPoly
-- name    : MIPRE_Background_LIDT_BlockPoly
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:32.409604+00:00
-- url     : https://prove2.me/theorems/e2c4d14c-21c5-4202-a75a-6d3ce5624f3d
-- title:
--   Definitions of BlockPoly: A polynomial on a block of the variables A coefficient vector in `n` variables read on a block of them, as a…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.BlockPoly` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A polynomial on a block of the variables. A coefficient vector in `n` variables read on a block of them, as a coefficient vector in the block's `n'` variables (`LowIndDegPoly.blockPoly`), and the exponent vectors that carry it (`expandIdx`). Moved from `MIPRE/Background/QLD/Complete.lean`, where the Pauli basis test's completion uses them, so that answer reduction can use them without importing that test.
--
--   **Definitions** (3): `MIPRE.LIDT.LowIndDegPoly.blockPoly` (**A coefficient vector read on a block of the variables**, as a coefficient vector on the block.); `MIPRE.LIDT.LowIndDegPoly.liftIdx` (**A coefficient vector in a block's variables, placed on the block**: zero on every monomial that reads a variable off the block.); `MIPRE.LIDT.expandIdx` (The exponent vector on `Fin n` carried by the injection `idx` from one on `Fin n'`, zero off the range.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.BlockPoly` (`MIPRE/Background/LIDT/BlockPoly.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/BlockPoly.lean; blueprint lem:qld-global-complete

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/BlockPoly.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game

/-!
# A polynomial on a block of the variables

A coefficient vector in `n` variables read on a block of them, as a coefficient vector in the
block's `n'` variables (`LowIndDegPoly.blockPoly`), and the exponent vectors that carry it
(`expandIdx`). Moved from `MIPRE/Background/QLD/Complete.lean`, where the Pauli basis test's
completion uses them, so that answer reduction can use them without importing that test.
-/

noncomputable section

/-! ## A polynomial on a block of the variables -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n n' d : ℕ}

/-- The exponent vector on `Fin n` carried by the injection `idx` from one on `Fin n'`, zero off
the range. -/
def expandIdx (idx : Fin n' → Fin n) (e' : Fin n' → Fin (d + 1)) : Fin n → Fin (d + 1) :=
  fun k => if h : ∃ j, idx j = k then e' h.choose else 0

/-- **A coefficient vector read on a block of the variables**, as a coefficient vector on the
block. -/
def LowIndDegPoly.blockPoly (idx : Fin n' → Fin n) (H : LowIndDegPoly (F := F) (m := n) (d := d)) :
    LowIndDegPoly (F := F) (m := n') (d := d) :=
  fun e' => H (expandIdx idx e')

/-- **A coefficient vector in a block's variables, placed on the block**: zero on every monomial
that reads a variable off the block. -/
def LowIndDegPoly.liftIdx (idx : Fin n' → Fin n) (g : LowIndDegPoly (F := F) (m := n') (d := d)) :
    LowIndDegPoly (F := F) (m := n) (d := d) :=
  fun e => if ∀ k, (∀ j, idx j ≠ k) → e k = 0 then g (fun j => e (idx j)) else 0

end MIPRE.LIDT

end


