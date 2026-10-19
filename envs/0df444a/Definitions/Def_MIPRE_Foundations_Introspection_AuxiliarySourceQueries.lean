-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
-- name    : MIPRE_Foundations_Introspection_AuxiliarySourceQueries
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:22.413871+00:00
-- url     : https://prove2.me/theorems/b6ca6840-0172-4c1a-8670-449b38583daa
-- title:
--   Definitions of AuxiliarySourceQueries: Executable source queries and matrix reconstruction The clock is supplied once as unary data
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliarySourceQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable source queries and matrix reconstruction. The clock is supplied once as unary data. Matrix reconstruction queries the linear map on the standard basis and transposes those columns. All operations are polynomial in the explicit clock, source text, and register length. Correctness is used only after the prefix scan establishes the source interface's attained-prefix premise.
--
--   **Definitions** (11): `MIPRE.Introspection.AuxiliarySource.Context`; `MIPRE.Introspection.AuxiliarySource.budget`; `MIPRE.Introspection.AuxiliarySource.factor`; `MIPRE.Introspection.AuxiliarySource.index`; `MIPRE.Introspection.AuxiliarySource.inputPrefix`; `MIPRE.Introspection.AuxiliarySource.level`; `MIPRE.Introspection.AuxiliarySource.linear` (Read a returned bit string; malformed results also terminate.); `MIPRE.Introspection.AuxiliarySource.player`; `MIPRE.Introspection.AuxiliarySource.query`; `MIPRE.Introspection.AuxiliarySource.queryInput`; `MIPRE.Introspection.AuxiliarySource.source`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliarySourceQueries` (`MIPRE/Foundations/Introspection/AuxiliarySourceQueries.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliarySourceQueries.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliarySourceQueries.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedQueryProgram
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode

/-! # Executable source queries and matrix reconstruction

The clock is supplied once as unary data. Matrix reconstruction queries the
linear map on the standard basis and transposes those columns. All operations
are polynomial in the explicit clock, source text, and register length.
Correctness is used only after the prefix scan establishes the source
interface's attained-prefix premise.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliarySource
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear

abbrev Context := Unary × Prog × ℕ × Bool × ℕ × BitStr

def budget : PolyTimeFun Context Unary := fst
def source : PolyTimeFun Context Prog := fst.comp snd
def index : PolyTimeFun Context ℕ := fst.comp (snd.comp snd)
def player : PolyTimeFun Context Bool := fst.comp (snd.comp (snd.comp snd))
def level : PolyTimeFun Context ℕ := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def inputPrefix : PolyTimeFun Context BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def queryInput (kind : ℕ) : PolyTimeFun (BitStr × Context) Data :=
  encoded.comp ((index.comp snd).pair ((const kind).pair ((player.comp snd).pair
    ((level.comp snd).pair ((inputPrefix.comp snd).pair fst)))))

def query (U : ClockedUniversalMachine) (kind : ℕ) : PolyTimeFun (BitStr × Context) Data :=
  (ClockedQuery.run U).comp ((budget.comp snd).pair ((source.comp snd).pair (queryInput kind)))

/-- Read a returned bit string; malformed results also terminate. -/
def linear (U : ClockedUniversalMachine) : PolyTimeFun (BitStr × Context) BitStr :=
  readBits.comp (treeTail.comp (query U 2))

def factor (U : ClockedUniversalMachine) : PolyTimeFun Context BitStr :=
  (readBits.comp (treeTail.comp (query U 3))).comp ((const []).pair (PolyTimeFun.id _))

end MIPRE.Introspection.AuxiliarySource
end


