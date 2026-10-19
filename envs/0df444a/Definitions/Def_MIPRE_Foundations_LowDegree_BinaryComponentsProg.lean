-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
-- name    : MIPRE_Foundations_LowDegree_BinaryComponentsProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:29.088339+00:00
-- url     : https://prove2.me/theorems/0aabd7c0-60f6-41ef-a766-c9bf70535999
-- title:
--   Definitions of BinaryComponentsProg: Polynomial-time fixed-space component separation
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryComponentsProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial-time fixed-space component separation
--
--   **Definitions** (5): `MIPRE.LowDegree.BinaryLinear.flattenBitsProg`; `MIPRE.LowDegree.BinaryLinear.keepRowProg`; `MIPRE.LowDegree.BinaryLinear.nonzeroRowProg`; `MIPRE.LowDegree.BinaryLinear.splitBitsCappedProg`; `MIPRE.LowDegree.BinaryLinear.splitBitsProg`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `splitBitsCappedProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryComponentsProg` (`MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 33 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents

/-! # Polynomial-time fixed-space component separation -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

def nonzeroRowProg : PolyTimeFun BitStr Bool :=
  congr (ite (SAT.ArrayProg.eqBits.comp ((PolyTimeFun.id _).pair (map (const false))))
    (const false) (const true)) nonzeroRow (by
      intro v
      change (if decide (v = zeroRow v) then false else true) = decide (¬v = zeroRow v)
      rw [decide_not]
      cases decide (v = zeroRow v) <;> rfl)

def keepRowProg : PolyTimeFun BitStr (List BitStr) :=
  ite nonzeroRowProg (cons (PolyTimeFun.id _) (const [])) (const [])

def splitBitsProg : PolyTimeFun (BitStr × BitStr) (List BitStr) :=
  congr (append.comp ((keepRowProg.comp groupMulBitsProg).pair
    (keepRowProg.comp (BinaryPolynomial.xorBitsProg.comp (fst.pair groupMulBitsProg)))))
    (fun p => splitBits p.1 p.2) (by
      rintro ⟨e, b⟩
      change (if nonzeroRow (groupMulBitsProg (e, b)) then [groupMulBitsProg (e, b)] else []) ++
        (if nonzeroRow (BinaryPolynomial.xorBits e (groupMulBitsProg (e, b))) then
          [BinaryPolynomial.xorBits e (groupMulBitsProg (e, b))] else []) = _
      unfold splitBits
      split <;> split <;> simp_all)

def flattenBitsProg : PolyTimeFun (List (List BitStr)) (List BitStr) :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

def splitBitsCappedProg : PolyTimeFun (Unary × List BitStr × BitStr) (List BitStr) :=
  take.comp ((flattenBitsProg.comp ((mapWith splitBitsProg).comp snd)).pair fst)

@[simp] theorem splitBitsCappedProg_apply (u : Unary) (l : List BitStr) (b : BitStr) :
    splitBitsCappedProg (u, l, b) = splitBitsCapped u l b := by
  change (List.flatten (l.map (fun e => splitBits e b))).take u.length = _
  simp only [splitBitsCapped, List.flatMap_def]

end MIPRE.LowDegree.BinaryLinear

end


