-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
-- name    : MIPRE_Foundations_CL_DetypingDeciderRoute
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:03:34.915988+00:00
-- url     : https://prove2.me/theorems/6a535885-2717-41d6-bcf4-d4a0ed5fc2c5
-- title:
--   Definitions of DetypingDeciderRoute: The executable detyping decision router This is an explicit ambient adaptation of `types.tex`'s detyped decider
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingDeciderRoute` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The executable detyping decision router. This is an explicit ambient adaptation of `types.tex`'s detyped decider. Canonical field encodings and question dimensions are checked first. An outer answer cutoff is enforced globally, as required by the ambient verifier budget. Within that cutoff nonedge views accept, and edge views use the source typed answer cutoff before invoking the typed decider. No uniform graph compilation or absolute source-model timeout bound is claimed here. Thus malformed graph patterns in binary questions accept within the outer cutoff, while noncanonical raw data…
--
--   **Definitions** (18): `MIPRE.CL.Detyping.DeciderProgram.aReader`; `MIPRE.CL.Detyping.DeciderProgram.bReader`; `MIPRE.CL.Detyping.DeciderProgram.context` (A raw input context after the dimension and cutoff routines have returned.); `MIPRE.CL.Detyping.DeciderProgram.dimensionReader`; `MIPRE.CL.Detyping.DeciderProgram.edgeAction` (The finite graph recognition table is an actual ambient program.); `MIPRE.CL.Detyping.DeciderProgram.edgeData`; `MIPRE.CL.Detyping.DeciderProgram.indexReader`; `MIPRE.CL.Detyping.DeciderProgram.innerReader`; `MIPRE.CL.Detyping.DeciderProgram.inputReader`; `MIPRE.CL.Detyping.DeciderProgram.lengthNat`; `MIPRE.CL.Detyping.DeciderProgram.outerReader`; `MIPRE.CL.Detyping.DeciderProgram.post` (An arbitrary typed output is accepted exactly when it is the canonical Boolean true.); `MIPRE.CL.Detyping.DeciderProgram.route` (All routing and format checks are concrete polynomial-time ambient computations.); `MIPRE.CL.Detyping.DeciderProgram.routeResult` (The precise routing rule, including every malformed-input branch.); `MIPRE.CL.Detyping.DeciderProgram.selectedEdge` (Recognize a genuine ordered edge from the complete graph-view patterns.); `MIPRE.CL.Detyping.DeciderProgram.typedArgument` (The typed decider is called using the seven-field input convention from the source.); `MIPRE.CL.Detyping.DeciderProgram.xReader`; `MIPRE.CL.Detyping.DeciderProgram.yReader`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `lengthNat_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingDeciderRoute` (`MIPRE/Foundations/CL/DetypingDeciderRoute.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDeciderRoute.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderRoute.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
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

/-! # The executable detyping decision router

This is an explicit ambient adaptation of `types.tex`'s detyped decider.
Canonical field encodings and question dimensions are checked first. An outer answer cutoff is
enforced globally, as required by the ambient verifier budget. Within that
cutoff nonedge views accept, and edge views use the source typed answer
cutoff before invoking the typed decider. No uniform graph compilation or
absolute source-model timeout bound is claimed here.

Thus malformed graph patterns in binary questions accept within the outer
cutoff, while noncanonical raw data encodings reject. The latter convention
has no effect on the finite games, whose fields are binary strings.
-/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

set_option linter.unusedSectionVars false

open Cost Cost.PolyTimeFun Detyping.Program

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]

/-- Recognize a genuine ordered edge from the complete graph-view patterns. -/
def selectedEdge (E : T → T → Prop) [DecidableRel E]
    (x y : Graph.Coord T → 𝔽₂) : Option (T × T) :=
  match select E false x, select E true y with
  | some u, some v => if E u v ∧ x = view E false u ∧ y = view E true v then some (u, v) else none
  | _, _ => none

def edgeData (E : T → T → Prop) [DecidableRel E]
    (x y : Graph.Coord T → 𝔽₂) : Data :=
  match selectedEdge E x y with
  | none => .nil
  | some uv => .cons (encode uv.1) (encode uv.2)

/-- The finite graph recognition table is an actual ambient program. -/
def edgeAction (E : T → T → Prop) [DecidableRel E] :
    PolyTimeFun ((Fin (graphDim T) → 𝔽₂) × (Fin (graphDim T) → 𝔽₂)) Data :=
  finiteFunction fun p => edgeData E (pull graphEquiv.toEmbedding p.1) (pull graphEquiv.toEmbedding p.2)

def lengthNat : PolyTimeFun BitStr ℕ := ap₂ addUnary (const 0) length

@[simp] theorem lengthNat_apply (x : BitStr) : lengthNat x = x.length := by simp [lengthNat]

/-- A raw input context after the dimension and cutoff routines have returned. -/
def context (input : Data) (s inner outer : ℕ) : Data :=
  .cons (.cons input (encode s)) (encode (inner, outer))

def inputReader : PolyTimeFun Data Data := treeHead.comp treeHead
def indexReader : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp inputReader)
def xReader : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp inputReader))
def yReader : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp inputReader)))
def aReader : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp inputReader))))
def bReader : PolyTimeFun Data BitStr := readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp inputReader))))
def dimensionReader : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp treeHead)
def innerReader : PolyTimeFun Data ℕ := readNat.comp (treeHead.comp treeTail)
def outerReader : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp treeTail)

/-- The typed decider is called using the seven-field input convention from the source. -/
def typedArgument (n : ℕ) (u v : Data) (x y a b : BitStr) : Data :=
  .cons (encode n) (.cons u (.cons (encode x) (.cons v (encode (y, a, b)))))

/-- The precise routing rule, including every malformed-input branch. -/
def routeResult (E : T → T → Prop) [DecidableRel E] (c : Data) : Bool × Data :=
  let input := inputReader c
  let n := indexReader c
  let x := xReader c
  let y := yReader c
  let a := aReader c
  let b := bReader c
  let dim := graphDim T + dimensionReader c
  let inner := innerReader c
  let outer := outerReader c
  let edge := edgeData E (graphOfBits x) (graphOfBits y)
  if input = encode (n, x, y, a, b) ∧ x.length = dim ∧ y.length = dim ∧
      a.length ≤ outer ∧ b.length ≤ outer then
    if rawTruth edge then
      if a.length ≤ inner ∧ b.length ≤ inner then
        (true, .cons (typedArgument n (treeHead edge) (treeTail edge)
          (x.drop (graphDim T)) (y.drop (graphDim T)) a b) .nil)
      else (false, encode false)
    else (false, encode true)
  else (false, encode false)

/-- All routing and format checks are concrete polynomial-time ambient computations. -/
def route (E : T → T → Prop) [DecidableRel E] : PolyTimeFun Data (Bool × Data) :=
  let n := indexReader
  let x := xReader
  let y := yReader
  let a := aReader
  let b := bReader
  let canonical := encoded.comp (n.pair (x.pair (y.pair (a.pair b))))
  let dim := ap₂ addUnary dimensionReader (const (unary (graphDim T)))
  let edge := (edgeAction E).comp (((readVector (graphDim T)).comp x).pair ((readVector (graphDim T)).comp y))
  let x' := ap₂ drop x (const (unary (graphDim T)))
  let y' := ap₂ drop y (const (unary (graphDim T)))
  let request := ap₂ treePair (encoded.comp n) (ap₂ treePair (treeHead.comp edge)
    (ap₂ treePair (encoded.comp x') (ap₂ treePair (treeTail.comp edge)
      (encoded.comp (y'.pair (a.pair b))))))
  let call := (const true).pair (ap₂ treePair request (const Data.nil))
  let reject := const (false, encode false)
  ite (ap₂ treeEq inputReader canonical)
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp x) dim)
      (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp y) dim)
        (ite (ap₂ leNat (lengthNat.comp a) outerReader)
          (ite (ap₂ leNat (lengthNat.comp b) outerReader)
            (ite (rawTruthProg.comp edge)
              (ite (ap₂ leNat (lengthNat.comp a) innerReader)
                (ite (ap₂ leNat (lengthNat.comp b) innerReader) call reject) reject)
              (const (false, encode true))) reject) reject) reject) reject) reject

/-- An arbitrary typed output is accepted exactly when it is the canonical Boolean true. -/
def post : PolyTimeFun (Data × Data) Data :=
  encoded.comp (ap₂ treeEq snd (const (encode true)))

end MIPRE.CL.Detyping.DeciderProgram


