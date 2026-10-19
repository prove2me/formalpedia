-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparationCost
-- name    : MIPRE_Foundations_Introspection_DecisionPreparationCost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:52:34.169029+00:00
-- url     : https://prove2.me/theorems/a4944c5c-b10f-423a-8a10-c9a6ade2d043
-- title:
--   Definitions of DecisionPreparationCost: Uniform costs for one shared introspection resource preparation
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.DecisionPreparationCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Uniform costs for one shared introspection resource preparation
--
--   **Definitions** (12): `MIPRE.Introspection.DecisionPreparation.appendPoly` (Cost of appending a result, with input and subroutine costs bounded by fixed polynomials of the same resource parameter.); `MIPRE.Introspection.DecisionPreparation.boundsMajorant`; `MIPRE.Introspection.DecisionPreparation.boundsPoly`; `MIPRE.Introspection.DecisionPreparation.clockPoly`; `MIPRE.Introspection.DecisionPreparation.compiledPoly`; `MIPRE.Introspection.DecisionPreparation.firstPoly`; `MIPRE.Introspection.DecisionPreparation.fourthPoly`; `MIPRE.Introspection.DecisionPreparation.kernelPoly`; `MIPRE.Introspection.DecisionPreparation.pauliPoly`; `MIPRE.Introspection.DecisionPreparation.preparationPoly`; `MIPRE.Introspection.DecisionPreparation.secondPoly`; `MIPRE.Introspection.DecisionPreparation.thirdPoly`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `boundsMajorant_polyBounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.DecisionPreparationCost` (`MIPRE/Foundations/Introspection/DecisionPreparationCost.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 83 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/DecisionPreparationCost.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DecisionPreparationCost.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparation
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_costMajorant_polyBounded

/-! # Uniform costs for one shared introspection resource preparation -/

noncomputable section
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial

def boundsMajorant (c v : ℕ) : ℕ :=
  let h := PauliSamplerParameters.widthBound c v
  2 * PauliSamplerParameters.unaryMajorant v + 2 * (4*v+1) + 4*v+20 +
    ClockArithmetic.mulCost v v + (parameterSeed c).timeBound.eval (2*v+1) +
    (14*h+9 + (exponentBitsCost h + PauliSamplerParameters.unaryMajorant h+1) +
      parameterPost.timeBound.eval (6*h+5)+12) +
    (16*h+13 + exponentBitsCost h + boundsPost.timeBound.eval (8*h+9)+12)+4

theorem boundsMajorant_polyBounded (c : ℕ) : PolyBounded (boundsMajorant c) := by
  unfold boundsMajorant PauliSamplerParameters.widthBound PauliSamplerParameters.unaryMajorant
    ClockArithmetic.mulCost exponentBitsCost
  repeat' first
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.eval
    | apply PolyBounded.const
    | exact PolyBounded.id

/-- Cost of appending a result, with input and subroutine costs bounded by
fixed polynomials of the same resource parameter. -/
def appendPoly (arg : PolyTimeFun Data Data) (p q : Polynomial ℕ) : Polynomial ℕ :=
  (appendRoute arg).timeBound.comp p + 3 * arg.timeBound.comp p + 3 * p + q + q +
    treePair.timeBound.comp (p+q+1) + 18

def clockPoly : Polynomial ℕ := ClockArithmetic.clockCostPoly 5
def pauliPoly (c : ℕ) : Polynomial ℕ := (PauliSamplerParameters.costMajorant_polyBounded c).poly
def boundsPoly (c : ℕ) : Polynomial ℕ := (boundsMajorant_polyBounded c).poly
def firstPoly : Polynomial ℕ := appendPoly parameterInput X clockPoly
def secondPoly : Polynomial ℕ := firstPoly +
  appendPoly (inputRaw.comp treeHead) firstPoly ClockSimulation.reindexCostPoly + 1
def thirdPoly (c : ℕ) : Polynomial ℕ := secondPoly +
  appendPoly (parameterInput.comp (treeHead.comp treeHead)) secondPoly (pauliPoly c) + 1
def fourthPoly (c : ℕ) : Polynomial ℕ := thirdPoly c +
  appendPoly (parameterInput.comp (treeHead.comp (treeHead.comp treeHead)))
    (thirdPoly c) (boundsPoly c) + 1
def preparationPoly (c : ℕ) : Polynomial ℕ := fourthPoly c + finish.timeBound.comp (fourthPoly c) + 1

def kernelPoly (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : Polynomial ℕ :=
  preparationPoly c + kernel.timeBound.comp (preparationPoly c) + 1

def compiledPoly (c : ℕ) (kernel : PolyTimeFun KernelInput Bool) : Polynomial ℕ :=
  kernelPoly c kernel + X + 2

end MIPRE.Introspection.DecisionPreparation


