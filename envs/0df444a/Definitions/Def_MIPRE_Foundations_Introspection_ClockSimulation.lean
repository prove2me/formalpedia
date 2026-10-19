-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
-- name    : MIPRE_Foundations_Introspection_ClockSimulation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:57:12.461292+00:00
-- url     : https://prove2.me/theorems/ff5a8eda-0f41-45d2-bbc5-be343b46745c
-- title:
--   Definitions of ClockSimulation: Executable clocked simulation at the original exponential index The clock is computed at index `n`; the source program…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ClockSimulation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable clocked simulation at the original exponential index. The clock is computed at index `n`; the source program receives index `2^n`. Both transformations are actual programs. The repaired exponent-five bound preserves the original bounded decider on its legal question and answer cut.
--
--   **Definitions** (7): `MIPRE.Introspection.ClockSimulation.clockStage`; `MIPRE.Introspection.ClockSimulation.indexReader`; `MIPRE.Introspection.ClockSimulation.prog` (This program computes the growing budget, changes the source index, and simulates.); `MIPRE.Introspection.ClockSimulation.reindexProg`; `MIPRE.Introspection.ClockSimulation.reindexStage`; `MIPRE.Introspection.ClockSimulation.reindexed`; `MIPRE.Introspection.ClockSimulation.simulationInput`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ClockSimulation` (`MIPRE/Foundations/Introspection/ClockSimulation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 67 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ClockSimulation.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockSimulation.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect

/-! # Executable clocked simulation at the original exponential index

The clock is computed at index `n`; the source program receives index `2^n`.
Both transformations are actual programs. The repaired exponent-five bound
preserves the original bounded decider on its legal question and answer cut.
-/

noncomputable section

namespace MIPRE.Introspection.ClockSimulation

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def indexReader : PolyTimeFun Data ℕ := readNat.comp treeHead

def reindexed (x : Data) : Data := .cons (encode (2 ^ indexReader x)) (treeTail x)

def reindexProg : Prog :=
  .let_ indexReader.code (.let_ toUnaryProg (.let_ expBitsProg
    (.cons (.var 0) (callVar 3 treeTail.code))))

def clockStage (k lam : ℕ) : Prog :=
  Prog.routeOneCall ClockProgram.clockRoute (growingClock k lam).prog treePair

def simulationInput (source : Prog) : PolyTimeFun (Data × Data) Data where
  toFun p := .cons p.1 (.cons (encode source) p.2)
  code := .elim 0 .nil (.cons (.var 0) (.cons (.const (encode source)) (.var 1)))
  closed := by simp [WellScoped]
  timeBound := Polynomial.X + Polynomial.C (esize source + 4)
  computes p := by
    rcases p with ⟨ctx, r⟩
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ctx) (b := r) (by rfl)
      (Eval.cons (Eval.var_of_get (i := 0) (by simp))
        (Eval.cons (Eval.const _ _) (Eval.var_of_get (i := 1) (by simp))))⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod, esize_data]
    change _ ≤ ctx.size + r.size + 1 + ((encode source).size + 4)
    omega

def reindexStage (source : Prog) : Prog := callWithContext reindexProg (simulationInput source)

/-- This program computes the growing budget, changes the source index, and simulates. -/
def prog (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) : Prog :=
  .let_ (clockStage k lam) (.let_ (reindexStage source) U.univT)

end MIPRE.Introspection.ClockSimulation


