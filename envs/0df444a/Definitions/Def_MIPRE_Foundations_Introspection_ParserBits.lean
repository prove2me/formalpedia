-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
-- name    : MIPRE_Foundations_Introspection_ParserBits
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:04:44.43292+00:00
-- url     : https://prove2.me/theorems/28a4ddff-9b69-4266-9eb4-a354554c9103
-- title:
--   Definitions of ParserBits: The paper's binary tuple encoding These are binary strings inside answers, distinct from ambient `Data` encodings
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ParserBits` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The paper's binary tuple encoding. These are binary strings inside answers, distinct from ambient `Data` encodings. Each payload bit `b` is written `false,b`; each field ends in `true,false`. The polynomial-time candidate reader is deliberately permissive. The answer parser checks exact re-encoding before using any candidate.
--
--   **Definitions** (11): `MIPRE.Introspection.AnswerParser.doubleBits`; `MIPRE.Introspection.AnswerParser.doubleProg` (An actual ambient polynomial-time implementation of bit doubling.); `MIPRE.Introspection.AnswerParser.field`; `MIPRE.Introspection.AnswerParser.fieldProg`; `MIPRE.Introspection.AnswerParser.payload` (Candidate payload obtained by removing the presumed last delimiter pair.); `MIPRE.Introspection.AnswerParser.payloadProg`; `MIPRE.Introspection.AnswerParser.undouble` (Read the second bit of each pair, discarding a trailing unmatched bit.); `MIPRE.Introspection.AnswerParser.undoubleProg`; `_private.MIPRE.Foundations.Introspection.ParserBits.0.MIPRE.Introspection.AnswerParser.doubleStep`; `_private.MIPRE.Foundations.Introspection.ParserBits.0.MIPRE.Introspection.AnswerParser.readStep`; `_private.MIPRE.Foundations.Introspection.ParserBits.0.MIPRE.Introspection.AnswerParser.readStepFun`.
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `doubleBits_length`, `doubleProg_apply`, `fieldProg_apply`, `field_length`, `payloadProg_apply`, `payload_field`, `undoubleProg_apply`, `undouble_doubleBits`, `doubleStep_size`, `double_fold`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ParserBits` (`MIPRE/Foundations/Introspection/ParserBits.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ParserBits.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ParserBits.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute

/-! # The paper's binary tuple encoding

These are binary strings inside answers, distinct from ambient `Data` encodings.
Each payload bit `b` is written `false,b`; each field ends in `true,false`.
The polynomial-time candidate reader is deliberately permissive. The answer
parser checks exact re-encoding before using any candidate.
-/

noncomputable section

namespace MIPRE.Introspection.AnswerParser

open Cost Cost.PolyTimeFun Polynomial

def doubleBits : BitStr → BitStr
  | [] => []
  | b :: bs => false :: b :: doubleBits bs

def field (bs : BitStr) : BitStr := doubleBits bs ++ [true, false]

@[simp] theorem doubleBits_length (bs : BitStr) :
    (doubleBits bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [doubleBits, ih]; omega

@[simp] theorem field_length (bs : BitStr) : (field bs).length = 2 * bs.length + 2 := by
  simp [field]

def doubleStep : PolyTimeFun (BitStr × Bool) BitStr :=
  cons snd (cons (const false) fst)

theorem doubleStep_size (s : BitStr) (b : Bool) :
    esize (doubleStep (s, b)) ≤ esize s + (C 6).eval (esize b) := by
  cases b <;> simp [doubleStep] <;> omega

theorem double_fold (bs acc : BitStr) :
    (bs.foldl (fun s b => doubleStep (s, b)) acc).reverse =
      acc.reverse ++ doubleBits bs := by
  induction bs generalizing acc with
  | nil => simp [doubleBits]
  | cons b bs ih =>
    rw [List.foldl_cons, ih]
    simp [doubleStep, doubleBits, List.append_assoc]

/-- An actual ambient polynomial-time implementation of bit doubling. -/
def doubleProg : PolyTimeFun BitStr BitStr :=
  congr (reverse.comp ((foldlAdd doubleStep (C 6) doubleStep_size).comp
    ((PolyTimeFun.id BitStr).pair (const [])))) doubleBits (by
      intro bs
      simpa using double_fold bs [])

@[simp] theorem doubleProg_apply (bs : BitStr) : doubleProg bs = doubleBits bs := rfl

def fieldProg : PolyTimeFun BitStr BitStr :=
  ap₂ append doubleProg (const [true, false])

@[simp] theorem fieldProg_apply (bs : BitStr) : fieldProg bs = field bs := rfl

def readStepFun (s : Bool × BitStr) (b : Bool) : Bool × BitStr :=
  if s.1 then (false, b :: s.2) else (true, s.2)

def readStep : PolyTimeFun ((Bool × BitStr) × Bool) (Bool × BitStr) :=
  PolyTimeFun.ite (fst.comp fst)
    ((const false).pair (cons snd (snd.comp fst)))
    ((const true).pair (snd.comp fst))

theorem readStep_apply (s : Bool × BitStr) (b : Bool) :
    readStep (s, b) = readStepFun s b := by
  rcases s with ⟨p, bs⟩
  cases p <;> simp [readStep, readStepFun, PolyTimeFun.ite_apply]

theorem readStep_size (s : Bool × BitStr) (b : Bool) :
    esize (readStep (s, b)) ≤ esize s + (C 6).eval (esize b) := by
  rcases s with ⟨p, bs⟩
  cases p <;> cases b <;>
    simp [readStep_apply, readStepFun, esize_prod] <;> omega

/-- Read the second bit of each pair, discarding a trailing unmatched bit. -/
def undouble (bs : BitStr) : BitStr :=
  (bs.foldl readStepFun (false, [])).2.reverse

theorem read_double_fold (bs acc : BitStr) :
    (doubleBits bs).foldl readStepFun (false, acc) = (false, bs.reverse ++ acc) := by
  induction bs generalizing acc with
  | nil => simp [doubleBits]
  | cons b bs ih => simp [doubleBits, List.foldl_cons, readStepFun, ih, List.append_assoc]

@[simp] theorem undouble_doubleBits (bs : BitStr) : undouble (doubleBits bs) = bs := by
  simp [undouble, read_double_fold]

def undoubleProg : PolyTimeFun BitStr BitStr :=
  congr (reverse.comp (snd.comp ((foldlAdd readStep (C 6) readStep_size).comp
    ((PolyTimeFun.id BitStr).pair (const (false, [])))))) undouble (by
      intro bs
      simp [undouble, readStep_apply])

@[simp] theorem undoubleProg_apply (bs : BitStr) : undoubleProg bs = undouble bs := rfl

/-- Candidate payload obtained by removing the presumed last delimiter pair. -/
def payload (bs : BitStr) : BitStr := undouble (bs.take (bs.length - 2))

def payloadProg : PolyTimeFun BitStr BitStr :=
  undoubleProg.comp (ap₂ take (PolyTimeFun.id BitStr)
    (length.comp (ap₂ drop (PolyTimeFun.id BitStr) (const (unary 2)))))

@[simp] theorem payloadProg_apply (bs : BitStr) : payloadProg bs = payload bs := by
  simp [payloadProg, payload]

@[simp] theorem payload_field (bs : BitStr) : payload (field bs) = bs := by
  simp only [payload, field_length, Nat.add_sub_cancel]
  rw [← doubleBits_length, field, List.take_left]
  exact undouble_doubleBits bs

end MIPRE.Introspection.AnswerParser

end


