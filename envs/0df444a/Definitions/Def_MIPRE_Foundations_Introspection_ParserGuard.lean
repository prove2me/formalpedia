-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
-- name    : MIPRE_Foundations_Introspection_ParserGuard
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:38.544794+00:00
-- url     : https://prove2.me/theorems/ee65039a-69f4-4a51-a499-753be830a0b7
-- title:
--   Definitions of ParserGuard: Reject malformed introspection answers before a source call The input is `encode (n, answerA, answerB)`
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ParserGuard` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reject malformed introspection answers before a source call. The input is `encode (n, answerA, answerB)`. On two valid Introspect answers the source receives `encode (n, yA, yB, aA, aB)`. The supplied index is retained, so this wrapper can precede the exponential-index clock adapter. This module does not implement the register projection from `Q` coordinates to a source question space, or the other auxiliary edge tests.
--
--   **Definitions** (5): `MIPRE.Introspection.AnswerParser.callArgument`; `MIPRE.Introspection.AnswerParser.callArgumentProg`; `MIPRE.Introspection.AnswerParser.guardIndex`; `MIPRE.Introspection.AnswerParser.guardLeft`; `MIPRE.Introspection.AnswerParser.guardRight`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `callArgumentProg_apply`, `guardIndex_cons`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ParserGuard` (`MIPRE/Foundations/Introspection/ParserGuard.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 47 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ParserGuard.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ParserGuard.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode

/-! # Reject malformed introspection answers before a source call

The input is `encode (n, answerA, answerB)`. On two valid Introspect answers
the source receives `encode (n, yA, yB, aA, aB)`. The supplied index is retained,
so this wrapper can precede the exponential-index clock adapter. This module
does not implement the register projection from `Q` coordinates to a source
question space, or the other auxiliary edge tests.
-/

noncomputable section

namespace MIPRE.Introspection.AnswerParser

open Cost Cost.PolyTimeFun CL.Detyping.Program

def guardIndex : PolyTimeFun Data ℕ := readNat.comp treeHead
def guardLeft : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp treeTail)
def guardRight : PolyTimeFun Data BitStr := readBits.comp (treeTail.comp treeTail)

def callArgument (Q : ℕ) (x : Data) : Data :=
  let a := pairParts Q (guardLeft x)
  let b := pairParts Q (guardRight x)
  encode (guardIndex x, a.1, b.1, a.2, b.2)

def callArgumentProg (Q : ℕ) : PolyTimeFun Data Data :=
  let a := (pairPartsProg Q).comp guardLeft
  let b := (pairPartsProg Q).comp guardRight
  encoded.comp (guardIndex.pair ((fst.comp a).pair
    ((fst.comp b).pair ((snd.comp a).pair (snd.comp b)))))

@[simp] theorem callArgumentProg_apply (Q : ℕ) (x : Data) :
    callArgumentProg Q x = callArgument Q x := by
  simp [callArgumentProg, callArgument]

@[simp] theorem guardIndex_cons (n : ℕ) (d : Data) :
    guardIndex (.cons (encode n) d) = n := by simp [guardIndex, readNat_encode]

end MIPRE.Introspection.AnswerParser

end


