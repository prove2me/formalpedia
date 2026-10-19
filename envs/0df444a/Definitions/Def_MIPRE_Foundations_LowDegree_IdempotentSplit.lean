-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
-- name    : MIPRE_Foundations_LowDegree_IdempotentSplit
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:03:30.478015+00:00
-- url     : https://prove2.me/theorems/faaa94b1-3691-45e1-9089-a17862169215
-- title:
--   Definitions of IdempotentSplit: Deterministic refinement by binary idempotents
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.IdempotentSplit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Deterministic refinement by binary idempotents
--
--   **Definitions** (5): `MIPRE.LowDegree.ComponentFamily` (A finite complete family of nonzero orthogonal idempotents.); `MIPRE.LowDegree.DecidesComponent` (A component is wholly inside or outside a supplied idempotent.); `MIPRE.LowDegree.splitAllComponents` (Iterate the deterministic refinement over a fixed generating family.); `MIPRE.LowDegree.splitComponent` (Split a component by a fixed idempotent and omit its zero children.); `MIPRE.LowDegree.splitComponents` (Refine all current components in the fixed input order.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `instFactPrimeOfNatNat_mIPRE`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.IdempotentSplit` (`MIPRE/Foundations/LowDegree/IdempotentSplit.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 23 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/IdempotentSplit.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/IdempotentSplit.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents

/-! # Deterministic refinement by binary idempotents -/

noncomputable section

namespace MIPRE.LowDegree

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Split a component by a fixed idempotent and omit its zero children. -/
def splitComponent (e b : R) : List R :=
  [e * b, e * (1 - b)].filter (fun x => decide (x ≠ 0))

/-- A finite complete family of nonzero orthogonal idempotents. -/
structure ComponentFamily (l : List R) : Prop where
  nonzero : ∀ e ∈ l, e ≠ 0
  idempotent : ∀ e ∈ l, e * e = e
  orthogonal : l.Pairwise (fun e f => e * f = 0)
  sum_eq_one : l.sum = 1

/-- Refine all current components in the fixed input order. -/
def splitComponents (l : List R) (b : R) : List R := l.flatMap (fun e => splitComponent e b)

/-- A component is wholly inside or outside a supplied idempotent. -/
def DecidesComponent (e b : R) : Prop := e * b = 0 ∨ e * b = e

/-- Iterate the deterministic refinement over a fixed generating family. -/
def splitAllComponents (l bs : List R) : List R := bs.foldl splitComponents l

section BinarySpan

local instance instFactPrimeOfNatNat_mIPRE : Fact (Nat.Prime 2) := ⟨by decide⟩
variable [Algebra (ZMod 2) R]

end BinarySpan

end MIPRE.LowDegree

end


