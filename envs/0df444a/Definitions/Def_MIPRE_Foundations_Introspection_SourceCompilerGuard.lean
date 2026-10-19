-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
-- name    : MIPRE_Foundations_Introspection_SourceCompilerGuard
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:00:27.528809+00:00
-- url     : https://prove2.me/theorems/d4d4b4d9-29b5-4aec-b8e0-beac3f9d8350
-- title:
--   Definitions of SourceCompilerGuard: Dynamic source-question projection and internal answer cutoff The input carries `(n,Q,R,s,answerA,answerB)` with all…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SourceCompilerGuard` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Dynamic source-question projection and internal answer cutoff. The input carries `(n,Q,R,s,answerA,answerB)` with all four numbers in binary. The guard validates the paper's tuple encoding, the separate original-answer cutoff, and membership of both register strings in the zero-padded source question space. Only then does it invoke the source on the first `s` bits.
--
--   **Definitions** (21): `MIPRE.Introspection.SourceCompiler.GuardInput`; `MIPRE.Introspection.SourceCompiler.GuardReady`; `MIPRE.Introspection.SourceCompiler.InSource`; `MIPRE.Introspection.SourceCompiler.RawReady`; `MIPRE.Introspection.SourceCompiler.eight`; `MIPRE.Introspection.SourceCompiler.guardCheck`; `MIPRE.Introspection.SourceCompiler.inputDim`; `MIPRE.Introspection.SourceCompiler.inputIndex`; `MIPRE.Introspection.SourceCompiler.inputLeft`; `MIPRE.Introspection.SourceCompiler.inputQ`; `MIPRE.Introspection.SourceCompiler.inputR`; `MIPRE.Introspection.SourceCompiler.inputRight`; `MIPRE.Introspection.SourceCompiler.instDecidableGuardReady`; `MIPRE.Introspection.SourceCompiler.instDecidableInSource`; `MIPRE.Introspection.SourceCompiler.instDecidableRawReady`; `MIPRE.Introspection.SourceCompiler.leftParts`; `MIPRE.Introspection.SourceCompiler.projectedCall`; `MIPRE.Introspection.SourceCompiler.readInput`; `MIPRE.Introspection.SourceCompiler.rightParts`; `MIPRE.Introspection.SourceCompiler.sourceCheck`; `_private.MIPRE.Foundations.Introspection.SourceCompilerGuard.0.MIPRE.Introspection.SourceCompiler.andCheck`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eight_apply`, `readInput_encode`, `andCheck_iff`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SourceCompilerGuard` (`MIPRE/Foundations/Introspection/SourceCompilerGuard.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 72 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourceCompilerGuard.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourceCompilerGuard.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
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
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # Dynamic source-question projection and internal answer cutoff

The input carries `(n,Q,R,s,answerA,answerB)` with all four numbers in binary.
The guard validates the paper's tuple encoding, the separate original-answer
cutoff, and membership of both register strings in the zero-padded source
question space. Only then does it invoke the source on the first `s` bits.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

abbrev GuardInput := ℕ × ℕ × ℕ × ℕ × BitStr × BitStr

def inputIndex : PolyTimeFun GuardInput ℕ := fst
def inputQ : PolyTimeFun GuardInput ℕ := fst.comp snd
def inputR : PolyTimeFun GuardInput ℕ := fst.comp (snd.comp snd)
def inputDim : PolyTimeFun GuardInput ℕ := fst.comp (snd.comp (snd.comp snd))
def inputLeft : PolyTimeFun GuardInput BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def inputRight : PolyTimeFun GuardInput BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def leftParts : PolyTimeFun GuardInput (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (inputLeft.pair inputQ)
def rightParts : PolyTimeFun GuardInput (BitStr × BitStr) :=
  DynamicParser.pairParts.comp (inputRight.pair inputQ)

def InSource (s : ℕ) (y : BitStr) : Prop :=
  y.drop s = List.replicate (y.length - s) false

instance (s : ℕ) (y : BitStr) : Decidable (InSource s y) := inferInstanceAs (Decidable (_ = _))

def sourceCheck : PolyTimeFun (BitStr × ℕ) Bool :=
  let rest := DynamicParser.dropBits
  ap₂ treeEq (encoded.comp rest)
    (encoded.comp ((map (const false : PolyTimeFun Bool Bool)).comp rest))

def eight : PolyTimeFun ℕ ℕ :=
  (ap₂ natBit (const false) (PolyTimeFun.id ℕ)).comp
    ((ap₂ natBit (const false) (PolyTimeFun.id ℕ)).comp
      (ap₂ natBit (const false) (PolyTimeFun.id ℕ)))

@[simp] theorem eight_apply (n : ℕ) : eight n = 8*n := by simp [eight, Nat.bit_val]; omega

def andCheck {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const false)

theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp

def GuardReady (x : GuardInput) : Prop :=
  inputDim x ≤ inputQ x ∧ inputDim x ≤ inputR x ∧
  AnswerParser.pairValid (inputQ x) (inputR x) (inputLeft x) ∧
  AnswerParser.pairValid (inputQ x) (inputR x) (inputRight x) ∧
  InSource (inputDim x) (leftParts x).1 ∧ InSource (inputDim x) (rightParts x).1 ∧
  (inputLeft x).length < 8*inputQ x ∧ (inputRight x).length < 8*inputQ x

instance (x : GuardInput) : Decidable (GuardReady x) := inferInstanceAs (Decidable (_ ∧ _))

def guardCheck : PolyTimeFun GuardInput Bool :=
  andCheck (ap₂ leNat inputDim inputQ) <|
  andCheck (ap₂ leNat inputDim inputR) <|
  andCheck (DynamicParser.pairCheck.comp (inputLeft.pair (inputQ.pair inputR))) <|
  andCheck (DynamicParser.pairCheck.comp (inputRight.pair (inputQ.pair inputR))) <|
  andCheck (sourceCheck.comp ((fst.comp leftParts).pair inputDim)) <|
  andCheck (sourceCheck.comp ((fst.comp rightParts).pair inputDim)) <|
  andCheck (ap₂ leNat (inc.comp (lengthNat.comp inputLeft)) (eight.comp inputQ))
    (ap₂ leNat (inc.comp (lengthNat.comp inputRight)) (eight.comp inputQ))

def projectedCall : PolyTimeFun GuardInput Data :=
  encoded.comp (inputIndex.pair
    ((DynamicParser.takeBits.comp ((fst.comp leftParts).pair inputDim)).pair
      ((DynamicParser.takeBits.comp ((fst.comp rightParts).pair inputDim)).pair
        ((snd.comp leftParts).pair (snd.comp rightParts)))))

def readInput : PolyTimeFun Data GuardInput :=
  (readNat.comp treeHead).pair
    (((readNat.comp treeHead).comp treeTail).pair
      (((readNat.comp treeHead).comp (treeTail.comp treeTail)).pair
        (((readNat.comp treeHead).comp (treeTail.comp (treeTail.comp treeTail))).pair
          (((readBits.comp treeHead).comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))).pair
            (readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))))))))

@[simp] theorem readInput_encode (x : GuardInput) : readInput (encode x) = x := by
  rcases x with ⟨n,Q,R,s,a,b⟩
  simp [readInput, encode_prod, readNat_encode, readBits_encode]

def RawReady (x : Data) : Prop := x = encode (readInput x) ∧ GuardReady (readInput x)
instance (x : Data) : Decidable (RawReady x) := inferInstanceAs (Decidable (_ ∧ _))

end MIPRE.Introspection.SourceCompiler

end


