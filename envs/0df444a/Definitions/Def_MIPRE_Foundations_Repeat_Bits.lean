-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_Bits
-- name    : MIPRE_Foundations_Repeat_Bits
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:38:06.964091+00:00
-- url     : https://prove2.me/theorems/7f2c840c-8e6a-48a8-8882-cd86fd057573
-- title:
--   Definitions of Bits: Blocks of bit strings The repeated sampler of `thm:parallel-repetition` presents `k` copies of an input CL function on…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.Bits` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Blocks of bit strings. The repeated sampler of `thm:parallel-repetition` presents `k` copies of an input CL function on `𝔽₂^s` as one CL function on `𝔽₂^{k s}` (`CLFun.famSum`, along `finProdFinEquiv`), and its program handles vectors as bit strings cut into `k` consecutive blocks of `s` bits (`Data.chunk`). This module relates the two: the bits of a joined vector are the concatenation of the bits of its blocks (`toBits_join`), the `i`-th block of the vector read off a bit string is the vector read off the `i`-th chunk (`block_ofBits`), and likewise for indicator strings of register subspaces…
--
--   **Definitions** (1): `MIPRE.Cost.Data.bitsOf` (The bits denoted by a list of data (`bitOf`), the left inverse of encoding a bit string.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `chunk_nil`, `chunk_zero`, `bitsOf_map_ofBool`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.Bits` (`MIPRE/Foundations/Repeat/Bits.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/Bits.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Bits.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat

/-!
# Blocks of bit strings

The repeated sampler of `thm:parallel-repetition` presents `k` copies of an input CL function
on `𝔽₂^s` as one CL function on `𝔽₂^{k s}` (`CLFun.famSum`, along `finProdFinEquiv`), and its
program handles vectors as bit strings cut into `k` consecutive blocks of `s` bits
(`Data.chunk`). This module relates the two: the bits of a joined vector are the concatenation
of the bits of its blocks (`toBits_join`), the `i`-th block of the vector read off a bit
string is the vector read off the `i`-th chunk (`block_ofBits`), and likewise for indicator
strings of register subspaces (`indicatorBits_blockSet`).
-/

namespace MIPRE.CL

open Cost.Data (chunk)

variable {k s : ℕ}

@[simp] theorem chunk_zero {α : Type*} (l : List α) : chunk s 0 l = l.take s := by simp [chunk]

@[simp] theorem chunk_nil {α : Type*} (i : ℕ) : chunk s i ([] : List α) = [] := by
  simp [chunk]

end MIPRE.CL

namespace MIPRE.Cost

namespace Data

/-- The bits denoted by a list of data (`bitOf`), the left inverse of encoding a bit string. -/
def bitsOf (l : List Data) : BitStr := l.map bitOf

@[simp] theorem bitsOf_map_ofBool (x : BitStr) : bitsOf (x.map ofBool) = x := by
  simp [bitsOf, List.map_map, Function.comp_def]

end Data

end MIPRE.Cost


