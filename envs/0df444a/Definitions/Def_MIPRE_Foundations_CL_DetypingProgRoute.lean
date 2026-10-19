-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
-- name    : MIPRE_Foundations_CL_DetypingProgRoute
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:38.188805+00:00
-- url     : https://prove2.me/theorems/23737d81-76a5-4c04-bc2c-b232cd41803b
-- title:
--   Definitions of DetypingProgRoute: Executable routing of detyped queries The fixed finite graph is compiled into a table
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgRoute` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable routing of detyped queries. The fixed finite graph is compiled into a table. The variable content is processed by list operations and at most one call to the original typed sampler. Padding follows the supplied content vector, so malformed queries never cause an unbounded dimension allocation.
--
--   **Definitions** (25): `MIPRE.CL.Detyping.Program.Context`; `MIPRE.CL.Detyping.Program.GraphArgs`; `MIPRE.CL.Detyping.Program.GraphResult`; `MIPRE.CL.Detyping.Program.callResult`; `MIPRE.CL.Detyping.Program.content`; `MIPRE.CL.Detyping.Program.directResult`; `MIPRE.CL.Detyping.Program.graphAction`; `MIPRE.CL.Detyping.Program.graphArgs`; `MIPRE.CL.Detyping.Program.graphResult`; `MIPRE.CL.Detyping.Program.pIndex`; `MIPRE.CL.Detyping.Program.pKind`; `MIPRE.CL.Detyping.Program.pLevel`; `MIPRE.CL.Detyping.Program.pPlayer`; `MIPRE.CL.Detyping.Program.pU`; `MIPRE.CL.Detyping.Program.pY`; `MIPRE.CL.Detyping.Program.pad`; `MIPRE.CL.Detyping.Program.post`; `MIPRE.CL.Detyping.Program.route`; `MIPRE.CL.Detyping.Program.routeParsed`; `MIPRE.CL.Detyping.Program.routeResult`; `MIPRE.CL.Detyping.Program.typedRequest`; `MIPRE.CL.Detyping.Program.withPrefix`; `_private.MIPRE.Foundations.CL.DetypingProgRoute.0.MIPRE.CL.Detyping.Program.callP`; `_private.MIPRE.Foundations.CL.DetypingProgRoute.0.MIPRE.CL.Detyping.Program.directP`; `_private.MIPRE.Foundations.CL.DetypingProgRoute.0.MIPRE.CL.Detyping.Program.prefixP`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgRoute` (`MIPRE/Foundations/CL/DetypingProgRoute.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgRoute.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgRoute.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
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

/-! # Executable routing of detyped queries

The fixed finite graph is compiled into a table. The variable content is
processed by list operations and at most one call to the original typed
sampler. Padding follows the supplied content vector, so malformed queries
never cause an unbounded dimension allocation.
-/

noncomputable section

namespace MIPRE.CL.Detyping.Program

open Cost Cost.PolyTimeFun

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]

abbrev GraphArgs (T : Type*) [Fintype T] :=
  Bool × Bool × (Fin (graphDim T) → 𝔽₂) × (Fin (graphDim T) → 𝔽₂)
abbrev GraphResult := BitStr × BitStr × BitStr × Data

def graphResult (E : T → T → Prop) [DecidableRel E] (a : GraphArgs T) : GraphResult :=
  let g := pull graphEquiv.toEmbedding a.2.2.1
  let y := pull graphEquiv.toEmbedding a.2.2.2
  let L := Graph.presentation E a.1
  ((if a.2.1 then graphBits ((L.truncate 1).eval g) else graphBits (L.eval g)),
   graphBits (L.mapOfPrefix (if a.2.1 then 0 else 1) g y),
   indicatorBits ((L.factorOfPrefix (if a.2.1 then 0 else 1) g).map graphEquiv.toEmbedding),
   match select E a.1 g with
   | none => .nil
   | some t => .cons (encode t) .nil)

def graphAction (E : T → T → Prop) [DecidableRel E] : PolyTimeFun (GraphArgs T) GraphResult :=
  finiteFunction (graphResult E)

def pIndex : PolyTimeFun Parsed Data := fst
def pKind : PolyTimeFun Parsed ℕ := fst.comp snd
def pPlayer : PolyTimeFun Parsed Bool := fst.comp (snd.comp snd)
def pLevel : PolyTimeFun Parsed ℕ := fst.comp (snd.comp (snd.comp snd))
def pU : PolyTimeFun Parsed BitStr := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def pY : PolyTimeFun Parsed BitStr := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def graphArgs : PolyTimeFun Parsed (GraphArgs T) :=
  pPlayer.pair ((ap₂ SAT.ArrayProg.eqNat pLevel (const 1)).pair
    ((readVector (graphDim T)).comp pU |>.pair ((readVector (graphDim T)).comp pY)))

abbrev Context := Parsed × GraphResult

def content (g : ℕ) (u : BitStr) : BitStr := u.drop g
def pad (b : Bool) (u : BitStr) : BitStr := u.map (fun _ => b)
def directResult (u : BitStr) : Bool × Data := (false, encode u)
def withPrefix (preBits : BitStr) : Data := .cons .nil (encode preBits)
def callResult (arg ctx : Data) : Bool × Data := (true, .cons arg ctx)

def typedRequest (n typ : Data) (kind : ℕ) (w : Bool) (j : ℕ) (u y : BitStr) : Data :=
  .cons n (.cons typ (encode (kind, w, j, u, y)))

def routeResult (g : ℕ) (p : Parsed) (a : GraphResult) : Bool × Data :=
  let n := p.1
  let k := p.2.1
  let w := p.2.2.1
  let j := p.2.2.2.1
  let u := content g p.2.2.2.2.1
  let y := content g p.2.2.2.2.2
  let zeros := List.replicate g false
  let typ := treeHead a.2.2.2
  if k = 0 then callResult (.cons n .nil) .nil
  else if k = 1 then
    if j ≤ 2 then directResult (a.1 ++ pad false u)
    else if rawTruth a.2.2.2 then
      callResult (typedRequest n typ 1 w (j - 2) u []) (withPrefix a.1)
    else directResult (a.1 ++ pad false u)
  else if k = 2 then
    if j ≤ 2 then directResult (a.2.1 ++ pad false y)
    else if rawTruth a.2.2.2 then
      callResult (typedRequest n typ 2 w (j - 2) u y) (withPrefix zeros)
    else directResult (zeros ++ pad false y)
  else if k = 3 then
    if j ≤ 2 then directResult (a.2.2.1 ++ pad false u)
    else if rawTruth a.2.2.2 then
      callResult (typedRequest n typ 3 w (j - 2) u []) (withPrefix zeros)
    else directResult (zeros ++ pad (decide (j = 3)) u)
  else (false, .nil)

def directP (u : PolyTimeFun Context BitStr) : PolyTimeFun Context (Bool × Data) :=
  (const false).pair (encoded.comp u)

def callP (arg ctx : PolyTimeFun Context Data) : PolyTimeFun Context (Bool × Data) :=
  (const true).pair (ap₂ treePair arg ctx)

def prefixP (u : PolyTimeFun Context BitStr) : PolyTimeFun Context Data :=
  ap₂ treePair (const Data.nil) (encoded.comp u)

def routeParsed (g : ℕ) : PolyTimeFun Context (Bool × Data) :=
  let n := pIndex.comp fst
  let k := pKind.comp fst
  let w := pPlayer.comp fst
  let j := pLevel.comp fst
  let u := ap₂ drop (pU.comp fst) (const (unary g))
  let y := ap₂ drop (pY.comp fst) (const (unary g))
  let zeros := const (List.replicate g false)
  let zu := (map (const false)).comp u
  let zy := (map (const false)).comp y
  let marg := fst.comp snd
  let lin := fst.comp (snd.comp snd)
  let fac := fst.comp (snd.comp (snd.comp snd))
  let sel := snd.comp (snd.comp (snd.comp snd))
  let typ := treeHead.comp sel
  let chosen := rawTruthProg.comp sel
  let early := ap₂ leNat j (const 2)
  let r := ap₂ subUnary j (const (unary 2))
  let req := fun (kind : ℕ) (v : PolyTimeFun Context BitStr) =>
    ap₂ treePair n (ap₂ treePair typ
      (encoded.comp ((const kind).pair (w.pair (r.pair (u.pair v))))))
  ite (ap₂ SAT.ArrayProg.eqNat k (const 0))
    (callP (ap₂ treePair n (const Data.nil)) (const Data.nil))
    (ite (ap₂ SAT.ArrayProg.eqNat k (const 1))
      (ite early (directP (ap₂ append marg zu))
        (ite chosen (callP (req 1 (const [])) (prefixP marg)) (directP (ap₂ append marg zu))))
      (ite (ap₂ SAT.ArrayProg.eqNat k (const 2))
        (ite early (directP (ap₂ append lin zy))
          (ite chosen (callP (req 2 y) (prefixP zeros)) (directP (ap₂ append zeros zy))))
        (ite (ap₂ SAT.ArrayProg.eqNat k (const 3))
          (ite early (directP (ap₂ append fac zu))
            (ite chosen (callP (req 3 (const [])) (prefixP zeros))
              (directP (ap₂ append zeros
                (ite (ap₂ SAT.ArrayProg.eqNat j (const 3)) ((map (const true)).comp u) zu)))))
          (const (false, Data.nil)))))

def route (E : T → T → Prop) [DecidableRel E] : PolyTimeFun Data (Bool × Data) :=
  (routeParsed (graphDim T)).comp
    ((PolyTimeFun.id Parsed).pair ((graphAction E).comp graphArgs) |>.comp parse)

def post (g : ℕ) : PolyTimeFun (Data × Data) Data :=
  ite (rawTruthProg.comp fst)
    (encoded.comp (ap₂ append (readBits.comp (treeTail.comp fst)) (readBits.comp snd)))
    (encoded.comp (ap₂ addUnary (readNat.comp snd) (const (unary g))))

end MIPRE.CL.Detyping.Program


