-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
-- name    : MIPRE_Foundations_Introspection_AuxiliaryReadProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:02:17.956169+00:00
-- url     : https://prove2.me/theorems/881030d9-8420-4c11-99de-8fbe5abaeaf3
-- title:
--   Definitions of AuxiliaryReadProgram: Executable full-register Introspect/Read comparison The binary register length and original answer cutoff are input…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliaryReadProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable full-register Introspect/Read comparison. The binary register length and original answer cutoff are input data. All register fields have the full padded length. In particular the Read dual answer is not required to vanish outside the original source register: the same-depth padding puts those coordinates in the first zero-map factor. The program checks canonical tuple syntax, the separate original answer cutoff, and the strict outer cutoff before comparing the two relevant fields.
--
--   **Definitions** (9): `MIPRE.Introspection.AuxiliaryProgram.andCheck`; `MIPRE.Introspection.AuxiliaryProgram.equal`; `MIPRE.Introspection.AuxiliaryProgram.outerCheck`; `MIPRE.Introspection.AuxiliaryProgram.pairLeft` (Full-Q pair format, including the original answer cutoff.); `MIPRE.Introspection.AuxiliaryProgram.pairRight`; `MIPRE.Introspection.AuxiliaryProgram.rawCheck` (Reject arbitrary noncanonical input trees before running the supplied pure check.); `MIPRE.Introspection.AuxiliaryProgram.readRight` (Full-Q Read format: there is deliberately no original-subspace test on the dual field.); `MIPRE.Introspection.AuxiliaryProgram.readingCheck` (The actual Introspect/Read branch, with all bounds supplied in binary.); `MIPRE.Introspection.AuxiliaryProgram.rightTriple`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `rawCheck_encode`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliaryReadProgram` (`MIPRE/Foundations/Introspection/AuxiliaryReadProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 114 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryReadProgram.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryReadProgram.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # Executable full-register Introspect/Read comparison

The binary register length and original answer cutoff are input data. All
register fields have the full padded length. In particular the Read dual
answer is not required to vanish outside the original source register: the
same-depth padding puts those coordinates in the first zero-map factor.
The program checks canonical tuple syntax, the separate original answer
cutoff, and the strict outer cutoff before comparing the two relevant fields.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryProgram

open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)

def andCheck {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const false)

def equal {α : Type*} [SizedEncoding α] {β : Type*} [SizedEncoding β]
    (f g : PolyTimeFun α β) : PolyTimeFun α Bool :=
  ap₂ treeEq (encoded.comp f) (encoded.comp g)

def rightTriple : PolyTimeFun GuardInput (BitStr × BitStr × BitStr) :=
  DynamicParser.tripleParts.comp (inputRight.pair inputQ)

def outerCheck : PolyTimeFun GuardInput Bool :=
  andCheck (ap₂ leNat (inc.comp (lengthNat.comp inputLeft)) (SourceCompiler.eight.comp inputQ))
    (ap₂ leNat (inc.comp (lengthNat.comp inputRight)) (SourceCompiler.eight.comp inputQ))

/-- Full-Q pair format, including the original answer cutoff. -/
def pairLeft : PolyTimeFun GuardInput Bool :=
  DynamicParser.pairCheck.comp (inputLeft.pair (inputQ.pair inputR))

def pairRight : PolyTimeFun GuardInput Bool :=
  DynamicParser.pairCheck.comp (inputRight.pair (inputQ.pair inputR))

/-- Full-Q Read format: there is deliberately no original-subspace test on the dual field. -/
def readRight : PolyTimeFun GuardInput Bool :=
  (DynamicParser.tripleCheck false).comp (inputRight.pair (inputQ.pair inputR))

/-- The actual Introspect/Read branch, with all bounds supplied in binary. -/
def readingCheck : PolyTimeFun GuardInput Bool :=
  andCheck outerCheck <| andCheck pairLeft <| andCheck readRight <|
    andCheck (equal (fst.comp leftParts) (fst.comp rightTriple))
      (equal (snd.comp leftParts) (snd.comp (snd.comp rightTriple)))

/-- Reject arbitrary noncanonical input trees before running the supplied pure check. -/
def rawCheck (check : PolyTimeFun GuardInput Bool) : PolyTimeFun Data Bool :=
  andCheck (equal (PolyTimeFun.id Data) (encoded.comp readInput)) (check.comp readInput)

@[simp] theorem rawCheck_encode (check : PolyTimeFun GuardInput Bool) (x : GuardInput) :
    rawCheck check (encode x) = check x := by
  simp [rawCheck, andCheck, equal, SourceCompiler.readInput_encode]

end MIPRE.Introspection.AuxiliaryProgram
end


