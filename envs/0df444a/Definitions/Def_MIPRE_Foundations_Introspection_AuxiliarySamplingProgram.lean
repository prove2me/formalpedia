-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
-- name    : MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:08:47.1642+00:00
-- url     : https://prove2.me/theorems/10e52ab4-3755-4d75-8e51-402c78e751ee
-- title:
--   Definitions of AuxiliarySamplingProgram: A total clocked full-register sampling check The program reads `(level, role, n, Q, R, s, left, right)` with binary…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliarySamplingProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A total clocked full-register sampling check. The program reads `(level, role, n, Q, R, s, left, right)` with binary parameters. Both answers contain Q-bit registers; only the Introspect register must vanish past s. The Sample seed is freely supported on the full register. The actual source marginal query receives its first s bits at index 2^n. A timeout or malformed source result rejects.
--
--   **Definitions** (17): `MIPRE.Introspection.AuxiliaryProgram.SamplingInput`; `MIPRE.Introspection.AuxiliaryProgram.SamplingRawReady`; `MIPRE.Introspection.AuxiliaryProgram.SamplingReady`; `MIPRE.Introspection.AuxiliaryProgram.instDecidableSamplingRawReady`; `MIPRE.Introspection.AuxiliaryProgram.instDecidableSamplingReady`; `MIPRE.Introspection.AuxiliaryProgram.readRole`; `MIPRE.Introspection.AuxiliaryProgram.readSamplingInput`; `MIPRE.Introspection.AuxiliaryProgram.samplingCall` (The marginal query contains the original seed length, not the padded length.); `MIPRE.Introspection.AuxiliaryProgram.samplingExpected`; `MIPRE.Introspection.AuxiliaryProgram.samplingFields`; `MIPRE.Introspection.AuxiliaryProgram.samplingLevel`; `MIPRE.Introspection.AuxiliaryProgram.samplingPost`; `MIPRE.Introspection.AuxiliaryProgram.samplingProg`; `MIPRE.Introspection.AuxiliaryProgram.samplingReady`; `MIPRE.Introspection.AuxiliaryProgram.samplingResult`; `MIPRE.Introspection.AuxiliaryProgram.samplingRole`; `MIPRE.Introspection.AuxiliaryProgram.samplingRoute`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `readRole_encode`, `readSamplingInput_encode`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliarySamplingProgram` (`MIPRE/Foundations/Introspection/AuxiliarySamplingProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 122 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliarySamplingProgram.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliarySamplingProgram.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # A total clocked full-register sampling check

The program reads `(level, role, n, Q, R, s, left, right)` with binary
parameters. Both answers contain Q-bit registers; only the Introspect
register must vanish past s. The Sample seed is freely supported on the
full register. The actual source marginal query receives its first s bits
at index 2^n. A timeout or malformed source result rejects.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)

abbrev SamplingInput := ℕ × Bool × GuardInput

def samplingLevel : PolyTimeFun SamplingInput ℕ := fst
def samplingRole : PolyTimeFun SamplingInput Bool := fst.comp snd
def samplingFields : PolyTimeFun SamplingInput GuardInput := snd.comp snd

def readRole : PolyTimeFun Data Bool := equal (PolyTimeFun.id Data) (const (encode true))

@[simp] theorem readRole_encode (w : Bool) : readRole (encode w) = w := by
  cases w <;> simp [readRole,equal]

def readSamplingInput : PolyTimeFun Data SamplingInput :=
  (readNat.comp treeHead).pair (((readRole.comp treeHead).comp treeTail).pair
    (readInput.comp (treeTail.comp treeTail)))

@[simp] theorem readSamplingInput_encode (x : SamplingInput) :
    readSamplingInput (encode x) = x := by
  rcases x with ⟨j,w,x⟩
  simp [readSamplingInput,encode_prod,readNat_encode]
  exact readRole_encode w

def SamplingReady (x : SamplingInput) : Prop :=
  1 ≤ x.1 ∧ inputDim x.2.2 ≤ inputQ x.2.2 ∧
  outerCheck x.2.2 = true ∧ pairLeft x.2.2 = true ∧ pairRight x.2.2 = true ∧
  SourceCompiler.InSource (inputDim x.2.2) (leftParts x.2.2).1 ∧
  (leftParts x.2.2).2 = (rightParts x.2.2).2

instance (x : SamplingInput) : Decidable (SamplingReady x) := inferInstanceAs (Decidable (_ ∧ _))

def samplingReady : PolyTimeFun SamplingInput Bool :=
  andCheck (ap₂ leNat (const 1) samplingLevel) <|
  (andCheck (ap₂ leNat inputDim inputQ) <|
    andCheck outerCheck <| andCheck pairLeft <| andCheck pairRight <|
      andCheck (SourceCompiler.sourceCheck.comp ((fst.comp leftParts).pair inputDim))
        (equal (snd.comp leftParts) (snd.comp rightParts))).comp samplingFields

def SamplingRawReady (x : Data) : Prop :=
  x = encode (readSamplingInput x) ∧ SamplingReady (readSamplingInput x)

instance (x : Data) : Decidable (SamplingRawReady x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The marginal query contains the original seed length, not the padded length. -/
def samplingCall : PolyTimeFun SamplingInput Data :=
  let fields := samplingFields
  let z := DynamicParser.takeBits.comp (((fst.comp rightParts).comp fields).pair (inputDim.comp fields))
  encoded.comp ((inputIndex.comp fields).pair
    ((const (1 : ℕ)).pair (samplingRole.pair (samplingLevel.pair (z.pair (const ([] : BitStr)))))))

def samplingRoute : PolyTimeFun Data (Bool × Data) :=
  let call := (const true).pair (ap₂ treePair (samplingCall.comp readSamplingInput) (PolyTimeFun.id Data))
  ite (andCheck (equal (PolyTimeFun.id Data) (encoded.comp readSamplingInput))
      (samplingReady.comp readSamplingInput)) call (const (false,encode false))

def samplingExpected : PolyTimeFun SamplingInput Data :=
  ap₂ treePair (const (encode true)) (encoded.comp (DynamicParser.takeBits.comp
    (((fst.comp leftParts).comp samplingFields).pair (inputDim.comp samplingFields))))

def samplingPost : PolyTimeFun (Data × Data) Data :=
  encoded.comp (equal snd (samplingExpected.comp (readSamplingInput.comp fst)))

def samplingProg (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) : Prog :=
  routeOneCall samplingRoute (ClockSimulation.prog k lam U S) samplingPost

def samplingResult (k lam : ℕ) (S : Prog) (x : SamplingInput) : Data :=
  clockedResult S (ClockSimulation.reindexed (samplingCall x))
    (ansBound k lam (ClockSimulation.indexReader (samplingCall x)))

end MIPRE.Introspection.AuxiliaryProgram
end


