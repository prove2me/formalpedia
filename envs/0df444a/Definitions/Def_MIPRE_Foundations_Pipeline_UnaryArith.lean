-- Prove2me | Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
-- name    : MIPRE_Foundations_Pipeline_UnaryArith
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:26.843002+00:00
-- url     : https://prove2.me/theorems/8d801825-0371-40d5-bb55-5783345c8815
-- title:
--   Definitions of UnaryArith: Unary arithmetic by loops The routines the pipeline's parameter computations need, whose running time is polynomial in…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Pipeline.UnaryArith` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Unary arithmetic by loops. The routines the pipeline's parameter computations need, whose running time is polynomial in the *value* of their input rather than its size: writing a binary number in unary (`toUnaryProg`) and raising a unary number to a binary power (`powProg`). Both are `whileProg` loops (`MIPRE/Foundations/Cost/While`) of polynomial-time steps.
--
--   **Definitions** (6): `MIPRE.Pipeline.powProg` (**The power**: `encode (b, e) ↦ encode (unary (|b|^e))`.); `MIPRE.Pipeline.powStep` (One step of the power, on `(e, acc, b)`: stop with `acc` at `e = 0`, else multiply by `b`.); `MIPRE.Pipeline.readUnary` (A unary numeral, read off its encoding.); `MIPRE.Pipeline.stageProg` (A stage of a routine: split the input into an argument and a context, run `p` on the argument, and combine the context with its answer.); `MIPRE.Pipeline.toUnaryProg` (**Binary to unary**: `encode x ↦ encode (unary x)`.); `MIPRE.Pipeline.toUnaryStep` (One step of the conversion, on `(x, acc)`: stop with `acc` at `x = 0`, else move one unit.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `rawList_encode`, `readUnary_encode`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Pipeline.UnaryArith` (`MIPRE/Foundations/Pipeline/UnaryArith.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 29 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/UnaryArith.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/UnaryArith.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_Cost_While

/-!
# Unary arithmetic by loops

The routines the pipeline's parameter computations need, whose running time is polynomial in the
*value* of their input rather than its size: writing a binary number in unary (`toUnaryProg`)
and raising a unary number to a binary power (`powProg`). Both are `whileProg` loops
(`MIPRE/Foundations/Cost/While`) of polynomial-time steps.
-/

namespace MIPRE.Pipeline

open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic

/-- A unary numeral, read off its encoding. -/
noncomputable def readUnary : PolyTimeFun Data Unary :=
  (map (const ())).comp (ofEncodeEq rawList encode_rawList)

theorem rawList_encode {α : Type*} [SizedEncoding α] (l : List α) :
    rawList (encode l) = l.map encode := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [encode_list_cons]; simp only [rawList, ih, List.map_cons]

@[simp] theorem readUnary_encode (u : Unary) : readUnary (encode u) = u := by
  change (rawList (encode u)).map (fun _ => ()) = u
  rw [rawList_encode, List.map_map]
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.map_cons, ih]

/-! ## Binary to unary -/

/-- One step of the conversion, on `(x, acc)`: stop with `acc` at `x = 0`, else move one unit. -/
noncomputable def toUnaryStep : PolyTimeFun Data (Bool × Data) :=
  let x := readNat.comp treeHead
  let acc := readUnary.comp treeTail
  ite (ap₂ SAT.ArrayProg.eqNat x (const 0)) ((const false).pair (encoded.comp acc))
    ((const true).pair (encoded.comp ((predN.comp x).pair ((const ()).cons acc))))

/-- **Binary to unary**: `encode x ↦ encode (unary x)`. -/
noncomputable def toUnaryProg : Prog :=
  seqProg (encoded.comp ((readNat).pair (const ([] : Unary)))).code (whileProg toUnaryStep)

/-! ## Powers -/

/-- One step of the power, on `(e, acc, b)`: stop with `acc` at `e = 0`, else multiply by `b`. -/
noncomputable def powStep : PolyTimeFun Data (Bool × Data) :=
  let e := readNat.comp treeHead
  let acc := readUnary.comp (treeHead.comp treeTail)
  let b := readUnary.comp (treeTail.comp treeTail)
  ite (ap₂ SAT.ArrayProg.eqNat e (const 0)) ((const false).pair (encoded.comp acc))
    ((const true).pair (encoded.comp ((predN.comp e).pair ((mulUnaryProg.comp (acc.pair b)).pair
      b))))

/-- **The power**: `encode (b, e) ↦ encode (unary (|b|^e))`. -/
noncomputable def powProg : Prog :=
  seqProg (encoded.comp ((readNat.comp treeTail).pair ((const (unary 1)).pair
    (readUnary.comp treeHead)))).code (whileProg powStep)

/-! ## Stages -/

/-- A stage of a routine: split the input into an argument and a context, run `p` on the
argument, and combine the context with its answer. -/
noncomputable def stageProg (pre : PolyTimeFun Data Data) (p : Prog)
    (post : PolyTimeFun (Data × Data) Data) : Prog :=
  seqProg pre.code (Prog.callWithContext p post)

end MIPRE.Pipeline


