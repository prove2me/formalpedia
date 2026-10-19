-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SamplerCost
-- name    : MIPRE_Foundations_Introspection_SamplerCost
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:27:00.629849+00:00
-- url     : https://prove2.me/theorems/dd6a6190-d9ea-4702-af35-d36fdaee5f7a
-- title:
--   Definitions of SamplerCost: Runtime transfer for the actual introspection sampler The auxiliary extension makes at most one Pauli-sampler call
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SamplerCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Runtime transfer for the actual introspection sampler. The auxiliary extension makes at most one Pauli-sampler call. Its explicit polynomial majorant has a degree independent of the input index and the number of hiding types. Composing this bound with the actual detyping compiler gives a polynomial query bound for the final five-level sampler.
--
--   **Definitions** (3): `MIPRE.Introspection.typedSamplerCoefficient`; `MIPRE.Introspection.typedSamplerCost`; `MIPRE.Introspection.typedSamplerDegree`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SamplerCost` (`MIPRE/Foundations/Introspection/SamplerCost.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 48 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SamplerCost.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SamplerCost.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.DeriveFintype
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
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Sampler
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_haltsWithin

/-! # Runtime transfer for the actual introspection sampler

The auxiliary extension makes at most one Pauli-sampler call. Its explicit
polynomial majorant has a degree independent of the input index and the number
of hiding types. Composing this bound with the actual detyping compiler gives
a polynomial query bound for the final five-level sampler.
-/

noncomputable section

namespace MIPRE.Introspection

open Cost CL Polynomial

def typedSamplerCost (n B k : ℕ) : Polynomial ℕ :=
  (Prog.routeCost SamplerProgram.route SamplerProgram.post B k).comp
    (X + C (esize n + 1))

def typedSamplerDegree (k : ℕ) : ℕ :=
  Prog.routeDegree SamplerProgram.route SamplerProgram.post k

def typedSamplerCoefficient (n B k : ℕ) : ℕ :=
  let Q := typedSamplerCost n B k
  ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i

variable {P : Type*} [SizedEncoding P]

section Detyped

variable [Fintype P] [DecidableEq P]

end Detyped
end MIPRE.Introspection


