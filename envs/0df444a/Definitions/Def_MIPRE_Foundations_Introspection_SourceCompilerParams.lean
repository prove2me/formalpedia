-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
-- name    : MIPRE_Foundations_Introspection_SourceCompilerParams
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:31:01.804309+00:00
-- url     : https://prove2.me/theorems/e79c4c35-a3a4-42c6-9796-b7d5a95b1587
-- title:
--   Definitions of SourceCompilerParams: Executable canonical register and answer bounds For `R = 2^(lambda*n)`, the paper uses `t = max 2 (lambda*n)`, `m =…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SourceCompilerParams` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable canonical register and answer bounds. For `R = 2^(lambda*n)`, the paper uses `t = max 2 (lambda*n)`, `m = 2^(size(c*t+1)-1)`, and `log q = c*size(t-1)+1`. Here `size(t-1)` is the integer ceiling of `log₂ t`. The universal even constant `c` is fixed; `lambda` and `n` are binary program inputs. The output is the binary pair `(Q,R)` with `Q = 2^m * log q`.
--
--   **Definitions** (15): `MIPRE.Introspection.SourceCompiler.affineUnary`; `MIPRE.Introspection.SourceCompiler.boundsPost`; `MIPRE.Introspection.SourceCompiler.boundsProg` (A fixed program computes the paper's binary `(Q,R)` from binary `(lambda,n)`.); `MIPRE.Introspection.SourceCompiler.canonicalLog`; `MIPRE.Introspection.SourceCompiler.clampLog`; `MIPRE.Introspection.SourceCompiler.fieldBits`; `MIPRE.Introspection.SourceCompiler.originalBound`; `MIPRE.Introspection.SourceCompiler.parameterPost`; `MIPRE.Introspection.SourceCompiler.parameterSeed` (Prepare the binary-power exponent, the original logarithm, and the field bit length.); `MIPRE.Introspection.SourceCompiler.powerUnaryProg`; `MIPRE.Introspection.SourceCompiler.readUnary` (Read a raw unary chain by its length; total on arbitrary data.); `MIPRE.Introspection.SourceCompiler.registerBits`; `MIPRE.Introspection.SourceCompiler.registerPower`; `MIPRE.Introspection.SourceCompiler.registerSizeProg` (Shift the binary field bit length by the computed unary register power.); `MIPRE.Introspection.SourceCompiler.unarySize`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `affineUnary_apply`, `bitsVal_zeros`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SourceCompilerParams` (`MIPRE/Foundations/Introspection/SourceCompilerParams.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 69 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourceCompilerParams.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourceCompilerParams.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_Prog_polyProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_polyProg_wellScoped

/-! # Executable canonical register and answer bounds

For `R = 2^(lambda*n)`, the paper uses `t = max 2 (lambda*n)`,
`m = 2^(size(c*t+1)-1)`, and `log q = c*size(t-1)+1`.
Here `size(t-1)` is the integer ceiling of `log₂ t`. The universal even
constant `c` is fixed; `lambda` and `n` are binary program inputs.
The output is the binary pair `(Q,R)` with `Q = 2^m * log q`.
-/

noncomputable section

namespace MIPRE.Introspection.SourceCompiler

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial

def canonicalLog (lam n : ℕ) : ℕ := max 2 (lam * n)
def registerPower (c lam n : ℕ) : ℕ := 2 ^ ((c * canonicalLog lam n + 1).size - 1)
def fieldBits (c lam n : ℕ) : ℕ := c * (canonicalLog lam n - 1).size + 1
def registerBits (c lam n : ℕ) : ℕ := 2 ^ registerPower c lam n * fieldBits c lam n
def originalBound (lam n : ℕ) : ℕ := 2 ^ (lam * n)

def affineUnary (c : ℕ) : PolyTimeFun Unary Unary where
  toFun u := unary (c * u.length + 1)
  code := polyProg [1, c]
  closed := polyProg_wellScoped _
  timeBound := (polyProg_runs [1, c]).choose
  computes u := by
    obtain ⟨t, ht, hr⟩ := (polyProg_runs [1, c]).choose_spec u.length []
    refine ⟨t, ht.trans (polynomial_eval_mono _ (length_le_esize_list u)), ?_⟩
    have he : encode u = Data.ofNat u.length := by rw [← unary_length u, encode_unary, length_unary]
    rw [he, encode_unary]
    simpa only [Prog.Runs, Data.polyEval, Nat.mul_zero, Nat.add_zero, Nat.mul_comm, Nat.add_comm] using hr

@[simp] theorem affineUnary_apply (c : ℕ) (u : Unary) :
    affineUnary c u = unary (c * u.length + 1) := rfl

def clampLog : PolyTimeFun Unary Unary :=
  ite (ap₂ leNat (const 2) unaryToBin) (PolyTimeFun.id Unary) (const (unary 2))

def unarySize : PolyTimeFun Unary Unary := length.comp (natBits.comp unaryToBin)

/-- Prepare the binary-power exponent, the original logarithm, and the field bit length. -/
def parameterSeed (c : ℕ) : PolyTimeFun Unary (Unary × Unary × Unary) :=
  (tail.comp (unarySize.comp ((affineUnary c).comp clampLog))).pair
    ((PolyTimeFun.id Unary).pair ((affineUnary c).comp (unarySize.comp (tail.comp clampLog))))

def powerUnaryProg : Prog := .let_ expBitsProg toUnaryProg

/-- Read a raw unary chain by its length; total on arbitrary data. -/
def readUnary : PolyTimeFun Data Unary := length.comp (ofEncodeEq rawList encode_rawList)

def parameterPost : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (treeHead.comp fst) (ap₂ treePair snd (treeTail.comp fst))

/-- Shift the binary field bit length by the computed unary register power. -/
def registerSizeProg : PolyTimeFun Data ℕ :=
  bitsValue.comp (ap₂ append ((map (const false : PolyTimeFun Unit Bool)).comp
      (readUnary.comp treeHead))
    (natBits.comp (unaryToBin.comp (readUnary.comp treeTail))))

theorem bitsVal_zeros (j : ℕ) (bs : BitStr) :
    bitsVal (List.replicate j false ++ bs) = 2 ^ j * bitsVal bs := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, bitsVal_cons, ih, Nat.bit_val, pow_succ]; ring

def boundsPost : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair (encoded.comp (registerSizeProg.comp fst)) snd

/-- A fixed program computes the paper's binary `(Q,R)` from binary `(lambda,n)`. -/
def boundsProg (c : ℕ) : Prog :=
  .let_ ClockArithmetic.bothUnary (.let_ mulProg (.let_ (parameterSeed c).code
    (.let_ (callWithContext powerUnaryProg parameterPost)
      (callWithContext expBitsProg boundsPost))))

end MIPRE.Introspection.SourceCompiler

end


