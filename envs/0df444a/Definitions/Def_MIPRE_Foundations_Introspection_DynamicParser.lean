-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
-- name    : MIPRE_Foundations_Introspection_DynamicParser
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:08:19.985702+00:00
-- url     : https://prove2.me/theorems/73f74936-616d-437b-9a88-6ba69251913c
-- title:
--   Definitions of DynamicParser: Uniform introspection tuple parsing with binary bounds One fixed program reads its register length and original-answer…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.DynamicParser` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniform introspection tuple parsing with binary bounds. One fixed program reads its register length and original-answer cutoff in binary. All format and cutoff specifications are exactly those of the fixed parser, but no parameter value is embedded as a unary program constant.
--
--   **Definitions** (5): `MIPRE.Introspection.DynamicParser.fieldOffset`; `MIPRE.Introspection.DynamicParser.pairCheck` (Introspect/Sample validation, uniformly in the binary bounds `Q` and `R`.); `MIPRE.Introspection.DynamicParser.pairParts` (Candidate pair fields, using the runtime binary register dimension.); `MIPRE.Introspection.DynamicParser.tripleCheck` (Read or Hide validation, with all numeric parameters supplied in binary.); `MIPRE.Introspection.DynamicParser.tripleParts`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fieldOffset_apply`, `pairParts_apply`, `tripleParts_apply`, `decide_and_if`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.DynamicParser` (`MIPRE/Foundations/Introspection/DynamicParser.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 42 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/DynamicParser.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DynamicParser.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # Uniform introspection tuple parsing with binary bounds

One fixed program reads its register length and original-answer cutoff in
binary. All format and cutoff specifications are exactly those of the fixed
parser, but no parameter value is embedded as a unary program constant.
-/

noncomputable section

namespace MIPRE.Introspection.DynamicParser

open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

def fieldOffset : PolyTimeFun ℕ ℕ := inc.comp (inc.comp (ap₂ natBit (const false) (PolyTimeFun.id ℕ)))

@[simp] theorem fieldOffset_apply (Q : ℕ) : fieldOffset Q = 2 * Q + 2 := by
  simp [fieldOffset, Nat.bit_val]

/-- Candidate pair fields, using the runtime binary register dimension. -/
def pairParts : PolyTimeFun (BitStr × ℕ) (BitStr × BitStr) :=
  let off := fieldOffset.comp snd
  (AnswerParser.payloadProg.comp (ap₂ takeBits fst off)).pair
    (AnswerParser.payloadProg.comp (ap₂ dropBits fst off))

@[simp] theorem pairParts_apply (bs : BitStr) (Q : ℕ) :
    pairParts (bs, Q) = AnswerParser.pairParts Q bs := by
  simp [pairParts, AnswerParser.pairParts]

def tripleParts : PolyTimeFun (BitStr × ℕ) (BitStr × BitStr × BitStr) :=
  (fst.comp pairParts).pair (pairParts.comp
    ((ap₂ dropBits fst (fieldOffset.comp snd)).pair snd))

@[simp] theorem tripleParts_apply (bs : BitStr) (Q : ℕ) :
    tripleParts (bs, Q) = AnswerParser.tripleParts Q bs := by
  simp [tripleParts, AnswerParser.tripleParts, AnswerParser.pairParts]

theorem decide_and_if (p q : Prop) [Decidable p] [Decidable q] :
    (if p then decide q else false) = decide (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-- Introspect/Sample validation, uniformly in the binary bounds `Q` and `R`. -/
def pairCheck : PolyTimeFun (BitStr × ℕ × ℕ) Bool :=
  let q : PolyTimeFun (BitStr × ℕ × ℕ) ℕ := fst.comp snd
  let r := snd.comp snd
  let parts := pairParts.comp (fst.pair q)
  ite (ap₂ treeEq (encoded.comp fst) (encoded.comp (AnswerParser.pairBitsProg.comp parts)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp parts)) q)
      (ap₂ leNat (lengthNat.comp (snd.comp parts)) r) (const false)) (const false)

/-- Read or Hide validation, with all numeric parameters supplied in binary. -/
def tripleCheck (exactLast : Bool) : PolyTimeFun (BitStr × ℕ × ℕ) Bool :=
  let q : PolyTimeFun (BitStr × ℕ × ℕ) ℕ := fst.comp snd
  let r := snd.comp snd
  let parts := tripleParts.comp (fst.pair q)
  let finalLength := lengthNat.comp (snd.comp (snd.comp parts))
  let lastCheck := if exactLast then ap₂ SAT.ArrayProg.eqNat finalLength r else ap₂ leNat finalLength r
  ite (ap₂ treeEq (encoded.comp fst) (encoded.comp (AnswerParser.tripleBitsProg.comp parts)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp parts)) q)
      (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp (snd.comp parts))) q)
        lastCheck (const false)) (const false)) (const false)

end MIPRE.Introspection.DynamicParser

end


