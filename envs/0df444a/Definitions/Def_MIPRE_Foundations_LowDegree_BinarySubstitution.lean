-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
-- name    : MIPRE_Foundations_LowDegree_BinarySubstitution
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:49.78789+00:00
-- url     : https://prove2.me/theorems/80fe95f3-7970-427a-9010-65a729faf86e
-- title:
--   Definitions of BinarySubstitution: Polynomial-time substitution of a unary-specified positive power
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinarySubstitution` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial-time substitution of a unary-specified positive power
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryPolynomial.substitutePowerBits` (Substitute `X^(u.length+1)` by inserting the requested number of zero coefficients.); `MIPRE.LowDegree.BinaryPolynomial.substitutePowerBitsProg` (A fixed ambient program for positive-power substitution on arbitrary coefficient lists.); `_private.MIPRE.Foundations.LowDegree.BinarySubstitution.0.MIPRE.LowDegree.BinaryPolynomial.coefficientBlockProg`; `_private.MIPRE.Foundations.LowDegree.BinarySubstitution.0.MIPRE.LowDegree.BinaryPolynomial.flattenCoefficientsProg`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `substitutePowerBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinarySubstitution` (`MIPRE/Foundations/LowDegree/BinarySubstitution.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 35 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySubstitution.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySubstitution.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg

/-! # Polynomial-time substitution of a unary-specified positive power -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Substitute `X^(u.length+1)` by inserting the requested number of zero coefficients.
The exponent is positive by construction; an empty unary parameter means substitution by `X`. -/
def substitutePowerBits (a : BitStr) (u : Unary) : BitStr :=
  normalizeBits (a.flatMap (fun b => b :: List.replicate u.length false))

noncomputable def coefficientBlockProg : PolyTimeFun (Bool × Unary) BitStr :=
  cons fst (replicate.comp (snd.pair (const false)))

noncomputable def flattenCoefficientsProg : PolyTimeFun (List BitStr) BitStr :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

/-- A fixed ambient program for positive-power substitution on arbitrary coefficient lists. -/
noncomputable def substitutePowerBitsProg : PolyTimeFun (BitStr × Unary) BitStr :=
  congr (normalizeBitsProg.comp (flattenCoefficientsProg.comp (mapWith coefficientBlockProg)))
    (fun s => substitutePowerBits s.1 s.2) (by
      intro s
      change normalizeBits (List.flatten (s.1.map
        (fun b => b :: List.replicate s.2.length false))) = _
      simp only [substitutePowerBits, List.flatMap_def])

@[simp] theorem substitutePowerBitsProg_apply (a : BitStr) (u : Unary) :
    substitutePowerBitsProg (a, u) = substitutePowerBits a u := rfl

end MIPRE.LowDegree.BinaryPolynomial


