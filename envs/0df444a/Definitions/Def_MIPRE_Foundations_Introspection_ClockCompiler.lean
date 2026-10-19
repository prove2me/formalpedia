-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
-- name    : MIPRE_Foundations_Introspection_ClockCompiler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:01:42.300703+00:00
-- url     : https://prove2.me/theorems/ffbcbda7-0684-45c8-bc34-e31d79ecc158
-- title:
--   Definitions of ClockCompiler: A binary compiler for the complete clocked source decider The compiler constructs the actual program syntax from the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ClockCompiler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A binary compiler for the complete clocked source decider. The compiler constructs the actual program syntax from the source description and binary parameter. Both compilation time and output description size are polynomial in their encoded lengths, for fixed exponent and universal machine.
--
--   **Definitions** (5): `MIPRE.Introspection.ClockSimulation.codeCall`; `MIPRE.Introspection.ClockSimulation.codeContext`; `MIPRE.Introspection.ClockSimulation.codeElim`; `MIPRE.Introspection.ClockSimulation.codeLet`; `MIPRE.Introspection.ClockSimulation.codeRoute`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ClockCompiler` (`MIPRE/Foundations/Introspection/ClockCompiler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 68 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ClockCompiler.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockCompiler.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation

/-! # A binary compiler for the complete clocked source decider

The compiler constructs the actual program syntax from the source description
and binary parameter. Both compilation time and output description size are
polynomial in their encoded lengths, for fixed exponent and universal machine.
-/

noncomputable section

namespace MIPRE.Introspection.ClockSimulation

open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program

def codeLet : PolyTimeFun (Prog × Prog) Prog :=
  cast (ap₂ treePair (const (Data.ofNat 4))
    (ap₂ treePair (encoded.comp fst) (encoded.comp snd)))
    (fun p => .let_ p.1 p.2) (by intro p; rfl)

def codeElim : PolyTimeFun (Prog × Prog) Prog :=
  cast (ap₂ treePair (const (Data.ofNat 3)) (ap₂ treePair (const Data.nil)
    (ap₂ treePair (encoded.comp fst) (encoded.comp snd))))
    (fun p => .elim 0 p.1 p.2) (by intro p; rfl)

def codeCall (i : ℕ) : PolyTimeFun Prog Prog :=
  ap₂ codeLet (const (.var i)) (PolyTimeFun.id Prog)

def codeContext : PolyTimeFun (Prog × Prog) Prog :=
  ap₂ codeLet (const fstProg)
    (ap₂ codeLet fst (ap₂ codeLet (const (.cons (callVar 2 sndProg) (.var 0))) snd))

def codeRoute (route : PolyTimeFun Data (Bool × Data)) (post : PolyTimeFun (Data × Data) Data) :
    PolyTimeFun Prog Prog :=
  ap₂ codeLet (const route.code)
    (ap₂ codeElim (const .nil) (ap₂ codeElim (const (.var 1))
      ((codeCall 3).comp (codeContext.comp ((PolyTimeFun.id Prog).pair (const post.code))))))

end MIPRE.Introspection.ClockSimulation


