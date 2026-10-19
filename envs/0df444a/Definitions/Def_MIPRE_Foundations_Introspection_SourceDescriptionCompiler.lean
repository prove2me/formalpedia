-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SourceDescriptionCompiler
-- name    : MIPRE_Foundations_Introspection_SourceDescriptionCompiler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:11.62644+00:00
-- url     : https://prove2.me/theorems/554b29cf-e0f5-42a0-b52c-7bf45090a5e6
-- title:
--   Definitions of SourceDescriptionCompiler: Uniformly bounded source descriptions for polynomial-time compilers The compiler accepts arbitrary source descriptions
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SourceDescriptionCompiler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniformly bounded source descriptions for polynomial-time compilers. The compiler accepts arbitrary source descriptions. Each description exceeding the supplied binary parameter is replaced by a fixed program before compilation. This leaves every bounded verifier unchanged and gives a uniform polynomial output-size bound in the parameter, including at zero.
--
--   **Definitions** (5): `MIPRE.Introspection.SourceDescriptionCompiler.Input`; `MIPRE.Introspection.SourceDescriptionCompiler.clamp` (Clamp sampler and decider independently while retaining the parameter.); `MIPRE.Introspection.SourceDescriptionCompiler.clampProgram` (Only an oversized description is replaced.); `MIPRE.Introspection.SourceDescriptionCompiler.compiler` (The final transformation is itself a single polynomial-time function.); `MIPRE.Introspection.SourceDescriptionCompiler.programSize` (Actual program encoding size, computed in binary after a linear-size count.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `clampProgram_apply`, `clamp_apply`, `programSize_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SourceDescriptionCompiler` (`MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Cost_Growth

/-! # Uniformly bounded source descriptions for polynomial-time compilers

The compiler accepts arbitrary source descriptions. Each description exceeding
the supplied binary parameter is replaced by a fixed program before compilation.
This leaves every bounded verifier unchanged and gives a uniform polynomial
output-size bound in the parameter, including at zero.
-/

noncomputable section
namespace MIPRE.Introspection.SourceDescriptionCompiler
open Cost Cost.PolyTimeFun Polynomial

abbrev Input := (Prog × Prog) × ℕ

/-- Actual program encoding size, computed in binary after a linear-size count. -/
def programSize : PolyTimeFun Prog ℕ := unaryToBin.comp (encodedSizeU Prog)

@[simp] theorem programSize_apply (p : Prog) : programSize p = esize p := by
  simp [programSize]

/-- Only an oversized description is replaced. The cutoff stays binary. -/
def clampProgram : PolyTimeFun (Prog × ℕ) Prog :=
  ite (leNat.comp ((programSize.comp fst).pair snd)) fst (const Prog.nil)

@[simp] theorem clampProgram_apply (p : Prog) (lam : ℕ) :
    clampProgram (p, lam) = if esize p ≤ lam then p else Prog.nil := by
  simp [clampProgram, PolyTimeFun.ite_apply]

/-- Clamp sampler and decider independently while retaining the parameter. -/
def clamp : PolyTimeFun Input Input :=
  ((clampProgram.comp ((fst.comp fst).pair snd)).pair
    (clampProgram.comp ((snd.comp fst).pair snd))).pair snd

@[simp] theorem clamp_apply (S D : Prog) (lam : ℕ) :
    clamp ((S, D), lam) = ((clampProgram (S, lam), clampProgram (D, lam)), lam) := rfl

variable {β : Type*} [SizedEncoding β]

/-- The final transformation is itself a single polynomial-time function. -/
def compiler (F : PolyTimeFun Input β) : PolyTimeFun Input β := F.comp clamp

end MIPRE.Introspection.SourceDescriptionCompiler


