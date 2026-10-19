-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
-- name    : MIPRE_Foundations_Introspection_ClockArithmetic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:29:01.946129+00:00
-- url     : https://prove2.me/theorems/aa284160-9565-49ed-98f6-2cb60bc72e95
-- title:
--   Definitions of ClockArithmetic: Executable arithmetic for the introspection clock One fixed program, for each constant exponent, reads binary `λ` and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ClockArithmetic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable arithmetic for the introspection clock. One fixed program, for each constant exponent, reads binary `λ` and `n` and writes the unary budget `2^((λ*n+1)^k)`. The large output is constructed by proved unary arithmetic programs; it is never embedded in the program text.
--
--   **Definitions** (7): `MIPRE.Introspection.ClockArithmetic.bothUnary`; `MIPRE.Introspection.ClockArithmetic.mulCost`; `MIPRE.Introspection.ClockArithmetic.powerBound`; `MIPRE.Introspection.ClockArithmetic.powerCoeffs`; `MIPRE.Introspection.ClockArithmetic.unaryCost`; `MIPRE.Introspection.ClockArithmetic.uniformCost`; `MIPRE.Introspection.ClockArithmetic.uniformProg`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ClockArithmetic` (`MIPRE/Foundations/Introspection/ClockArithmetic.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 64 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ClockArithmetic.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockArithmetic.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_Prog_polyProg_runs

/-! # Executable arithmetic for the introspection clock

One fixed program, for each constant exponent, reads binary `λ` and `n` and
writes the unary budget `2^((λ*n+1)^k)`. The large output is constructed by
proved unary arithmetic programs; it is never embedded in the program text.
-/

noncomputable section

namespace MIPRE.Introspection.ClockArithmetic

open Cost Cost.Prog Polynomial

def unaryCost (n : ℕ) : ℕ :=
  (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90)

def bothUnary : Prog :=
  .elim 0 .nil (.let_ (callVar 0 toUnaryProg)
    (.let_ (callVar 2 toUnaryProg) (.cons (.var 1) (.var 0))))

def powerCoeffs (k : ℕ) : List ℕ := List.replicate k 0 ++ [1]

def powerBound (k : ℕ) : Polynomial ℕ := (polyProg_runs (powerCoeffs k)).choose

def mulCost (a b : ℕ) : ℕ :=
  (b + 1) * ((a + 1) * (4 * a + 2 * (a * b) + 15) + 4 * a + 4 * (a * b) + 2 * b + 41) +
    2 * b + 10

def uniformProg (k : ℕ) : Prog :=
  .let_ bothUnary (.let_ mulProg (.let_ (.cons .nil (.var 0))
    (.let_ (polyProg (powerCoeffs k)) (.let_ expBitsProg toUnaryProg))))

def uniformCost (k lam n : ℕ) : ℕ :=
  let m := lam * n + 1
  let q := m ^ k
  unaryCost lam + unaryCost n + esize lam + esize n + 2 * lam + 2 * n + 20 +
    mulCost lam n + 2 * (lam * n) + 4 + (powerBound k).eval m +
    (q + 2) * (4 * q + 20) + unaryCost (ansBound k lam n) + 5

end MIPRE.Introspection.ClockArithmetic


