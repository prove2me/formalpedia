-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SamplerProgram
-- name    : MIPRE_Foundations_Introspection_SamplerProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:28:36.586177+00:00
-- url     : https://prove2.me/theorems/c159bfdb-921a-45f5-8a27-55e6209f65a4
-- title:
--   Definitions of SamplerProgram: The executable typed introspection sampler router Dimension queries and Pauli queries call the supplied sampler once
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SamplerProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The executable typed introspection sampler router. Dimension queries and Pauli queries call the supplied sampler once. Auxiliary queries write the zero vector or the appropriate factor indicator, using the length of the supplied vector. This total router needs no decoding of the ambient dimension and does not depend on the number of hiding types.
--
--   **Definitions** (6): `MIPRE.Introspection.SamplerProgram.aux`; `MIPRE.Introspection.SamplerProgram.auxResult`; `MIPRE.Introspection.SamplerProgram.post`; `MIPRE.Introspection.SamplerProgram.prog`; `MIPRE.Introspection.SamplerProgram.route`; `MIPRE.Introspection.SamplerProgram.routeResult`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SamplerProgram` (`MIPRE/Foundations/Introspection/SamplerProgram.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 46 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SamplerProgram.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SamplerProgram.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_CL_Detyping_Program_parse_query
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_halts
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect

/-! # The executable typed introspection sampler router

Dimension queries and Pauli queries call the supplied sampler once. Auxiliary
queries write the zero vector or the appropriate factor indicator, using the
length of the supplied vector. This total router needs no decoding of the
ambient dimension and does not depend on the number of hiding types.
-/

noncomputable section

namespace MIPRE.Introspection.SamplerProgram

open Cost Cost.PolyTimeFun CL CL.Detyping.Program

def auxResult (p : Parsed) : BitStr :=
  if p.2.1 = 2 then pad false p.2.2.2.2.2
  else if p.2.1 = 3 then pad (decide (p.2.2.2.1 = 1)) p.2.2.2.2.1
  else pad false p.2.2.2.2.1

def aux : PolyTimeFun Parsed BitStr :=
  ite (ap₂ SAT.ArrayProg.eqNat pKind (const 2)) ((map (const false)).comp pY)
    (ite (ap₂ SAT.ArrayProg.eqNat pKind (const 3))
      (ite (ap₂ SAT.ArrayProg.eqNat pLevel (const 1))
        ((map (const true)).comp pU) ((map (const false)).comp pU))
      ((map (const false)).comp pU))

def routeResult (x : Data) : Bool × Data :=
  let n := treeHead x
  let q := treeTail x
  if rawTruth q then
    if rawTruth (treeHead (treeHead q)) then
      directResult (auxResult (parse (.cons n (treeTail q))))
    else callResult (.cons n (.cons (treeTail (treeHead q)) (treeTail q))) .nil
  else callResult (.cons n .nil) .nil

def route : PolyTimeFun Data (Bool × Data) :=
  let n := treeHead
  let q := treeTail
  let typ := treeHead.comp q
  let body := treeTail.comp q
  let call := fun a : PolyTimeFun Data Data =>
    (const true).pair (ap₂ treePair a (const Data.nil))
  ite (rawTruthProg.comp q)
    (ite (rawTruthProg.comp (treeHead.comp typ))
      ((const false).pair (encoded.comp (aux.comp (parse.comp (ap₂ treePair n body)))))
      (call (ap₂ treePair n (ap₂ treePair (treeTail.comp typ) body))))
    (call (ap₂ treePair n (const Data.nil)))

def post : PolyTimeFun (Data × Data) Data := snd

def prog {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P) : Prog :=
  Prog.routeOneCall route S.prog post

end MIPRE.Introspection.SamplerProgram


