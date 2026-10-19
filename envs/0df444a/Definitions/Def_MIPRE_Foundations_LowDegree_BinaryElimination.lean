-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
-- name    : MIPRE_Foundations_LowDegree_BinaryElimination
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:57:38.938126+00:00
-- url     : https://prove2.me/theorems/e928e7ec-98eb-49b4-a9b5-02befaf89078
-- title:
--   Definitions of BinaryElimination: Binary elimination with coefficient certificates Each row carries both its vector and a coefficient vector describing…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryElimination` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary elimination with coefficient certificates. Each row carries both its vector and a coefficient vector describing that vector in the original generating family. Reduction XORs both components together. The program is uniformly polynomial-time even for malformed pivots and rows.
--
--   **Definitions** (13): `MIPRE.LowDegree.BinaryLinear.Pivot`; `MIPRE.LowDegree.BinaryLinear.RawPivot`; `MIPRE.LowDegree.BinaryLinear.RawRow`; `MIPRE.LowDegree.BinaryLinear.Represents` (A row carries a valid expression in a fixed original generating family.); `MIPRE.LowDegree.BinaryLinear.Row`; `MIPRE.LowDegree.BinaryLinear.pivotBits`; `MIPRE.LowDegree.BinaryLinear.reduceRows`; `MIPRE.LowDegree.BinaryLinear.reduceRowsProg` (Uniform, certificate-preserving binary elimination along a supplied pivot list.); `MIPRE.LowDegree.BinaryLinear.reduceStep`; `MIPRE.LowDegree.BinaryLinear.rowBits`; `MIPRE.LowDegree.BinaryLinear.typedReduce`; `MIPRE.LowDegree.BinaryLinear.typedReduceStep`; `_private.MIPRE.Foundations.LowDegree.BinaryElimination.0.MIPRE.LowDegree.BinaryLinear.reduceStepProg`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `reduceRowsProg_apply`, `reduceRows_width`, `reduceStep_width`, `reduceStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryElimination` (`MIPRE/Foundations/LowDegree/BinaryElimination.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 20 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryElimination.lean; blueprint lem:effective-binary-linear-algebra

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryElimination.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
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

/-!
# Binary elimination with coefficient certificates

Each row carries both its vector and a coefficient vector describing that vector
in the original generating family. Reduction XORs both components together.
The program is uniformly polynomial-time even for malformed pivots and rows.
-/

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

abbrev RawRow := BitStr × BitStr
abbrev RawPivot := ℕ × RawRow

def reduceStep (r : RawRow) (b : RawPivot) : RawRow :=
  if r.1.getD b.1 false then
    (BinaryPolynomial.xorBits r.1 b.2.1, BinaryPolynomial.xorBits r.2 b.2.2)
  else r

def reduceRows (b : List RawPivot) (r : RawRow) : RawRow := b.foldl reduceStep r

theorem reduceStep_width (r : RawRow) (b : RawPivot) :
    (reduceStep r b).1.length ≤ r.1.length ∧
    (reduceStep r b).2.length ≤ r.2.length := by
  unfold reduceStep
  split
  · simp only [BinaryPolynomial.length_xorBits]
    exact ⟨min_le_left _ _, min_le_left _ _⟩
  · exact ⟨le_rfl, le_rfl⟩

theorem reduceRows_width (b : List RawPivot) (r : RawRow) :
    (reduceRows b r).1.length ≤ r.1.length ∧
    (reduceRows b r).2.length ≤ r.2.length := by
  induction b generalizing r with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons p b ih =>
    obtain ⟨h₁, h₂⟩ := ih (reduceStep r p)
    obtain ⟨h₁', h₂'⟩ := reduceStep_width r p
    exact ⟨h₁.trans h₁', h₂.trans h₂'⟩

abbrev Row (n t : ℕ) := (Fin n → ZMod 2) × (Fin t → ZMod 2)
abbrev Pivot (n t : ℕ) := Fin n × Row n t

def rowBits {n t : ℕ} (r : Row n t) : RawRow := (vectorBits r.1, vectorBits r.2)

def pivotBits {n t : ℕ} (p : Pivot n t) : RawPivot := (p.1, rowBits p.2)

def typedReduceStep {n t : ℕ} (r : Row n t) (p : Pivot n t) : Row n t :=
  if r.1 p.1 = 1 then (r.1 + p.2.1, r.2 + p.2.2) else r

def typedReduce {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) : Row n t :=
  b.foldl typedReduceStep r

/-- A row carries a valid expression in a fixed original generating family. -/
def Represents {n t : ℕ} (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) : Prop := L r.2 = r.1

noncomputable def reduceStepProg : PolyTimeFun (RawRow × RawPivot) RawRow :=
  let pivot := fst.comp snd
  let v := fst.comp fst
  let w := snd.comp fst
  let bv := fst.comp (snd.comp snd)
  let bw := snd.comp (snd.comp snd)
  congr (ite ((SAT.ArrayProg.getD false).comp (pivot.pair v))
    ((BinaryPolynomial.xorBitsProg.comp (v.pair bv)).pair
      (BinaryPolynomial.xorBitsProg.comp (w.pair bw))) fst)
    (fun p => reduceStep p.1 p.2) (by intro p; rfl)

theorem reduceStep_bounded : FoldBounded reduceStepProg (5 * X + 5) := by
  intro l r pre post _
  change esize (reduceRows pre r) ≤ _
  obtain ⟨hv, hw⟩ := reduceRows_width pre r
  have hv0 := length_le_esize_list r.1
  have hw0 := length_le_esize_list r.2
  have hsv := esize_bitStr_le (reduceRows pre r).1
  have hsw := esize_bitStr_le (reduceRows pre r).2
  have hs : esize r = esize r.1 + esize r.2 + 1 := rfl
  rw [esize_prod]
  grw [hsv, hsw, hv, hw, hv0, hw0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Uniform, certificate-preserving binary elimination along a supplied pivot list. -/
noncomputable def reduceRowsProg : PolyTimeFun (List RawPivot × RawRow) RawRow :=
  congr (foldl reduceStepProg (5 * X + 5) reduceStep_bounded)
    (fun p => reduceRows p.1 p.2) (by intro p; rfl)

@[simp] theorem reduceRowsProg_apply (b : List RawPivot) (r : RawRow) :
    reduceRowsProg (b, r) = reduceRows b r := rfl

end MIPRE.LowDegree.BinaryLinear


