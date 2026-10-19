-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Formula
-- name    : MIPRE_Foundations_SAT_Formula
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:00.071888+00:00
-- url     : https://prove2.me/theorems/90728ca4-4628-4ed5-a957-13fb95d88510
-- title:
--   Definitions of Formula: Boolean formulas and their circuits A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Formula` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Boolean formulas and their circuits. A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants. Its post-order flattening (`Fml.flattenAt`) is a circuit in which every gate is read at most once (input bits are read through fresh `input` gates, which `Circuit.WellFormed` does not count), so a formula's circuit is well-formed whatever the formula (`Fml.toCircuit_wellFormed`), and computes the formula (`Fml.eval_toCircuit`). The describer of the succinct Cook–Levin theorem is built as a formula, which confines the circuit bookkeeping to this file…
--
--   **Definitions** (21): `MIPRE.SAT.Fml` (Boolean formulas over input bits.); `MIPRE.SAT.Fml.InputsLt` (Every input bit read is below `n`.); `MIPRE.SAT.Fml.Node` (The nodes of the post-order (reverse Polish) serialization of a formula.); `MIPRE.SAT.Fml.Node.instSizedEncoding`; `MIPRE.SAT.Fml.Node.ofData?` (Decoding nodes.); `MIPRE.SAT.Fml.Node.toData` (Nodes as data: a unary tag and the payload.); `MIPRE.SAT.Fml.andF`; `MIPRE.SAT.Fml.constF`; `MIPRE.SAT.Fml.eval` (The value of a formula on the input bits `x`.); `MIPRE.SAT.Fml.flattenAt` (The post-order gate list of a formula whose first gate is at position `base`: the output gate is the last one, at `base + size - 1`.); `MIPRE.SAT.Fml.inpF` (The constructors as polynomial-time functions.); `MIPRE.SAT.Fml.instSizedEncoding` (Formulas encode as their post-order serializations, so that a program builds a formula by appending lists.); `MIPRE.SAT.Fml.notF`; `MIPRE.SAT.Fml.orF`; `MIPRE.SAT.Fml.parse` (Parsing a post-order serialization.); `MIPRE.SAT.Fml.parseStep` (One step of parsing a post-order serialization with a stack of formulas (a malformed input leaves the stack unchanged).); `MIPRE.SAT.Fml.refCount` (The number of references to `u` in a gate list.); `MIPRE.SAT.Fml.rpn` (The post-order serialization of a formula.); `MIPRE.SAT.Fml.rpnF` (The serialization, as a polynomial-time function (the encoding is the same).); `MIPRE.SAT.Fml.size` (The number of nodes: the number of gates of the circuit.); and -4 more.
--
--   **Embedded lemmas** (18): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `encode_const`, `encode_inp`, `ofData?_toData`, `andF_apply`, `constF_apply`, `foldl_parseStep_rpn`, `inpF_apply`, `length_flattenAt`, `length_rpn`, `notF_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Formula` (`MIPRE/Foundations/SAT/Formula.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 10 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Formula.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Formula.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary

/-!
# Boolean formulas and their circuits

A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants. Its
post-order flattening (`Fml.flattenAt`) is a circuit in which every gate is read at most once
(input bits are read through fresh `input` gates, which `Circuit.WellFormed` does not count),
so a formula's circuit is well-formed whatever the formula (`Fml.toCircuit_wellFormed`), and
computes the formula (`Fml.eval_toCircuit`). The describer of the succinct Cook–Levin
theorem is built as a formula, which confines the circuit bookkeeping to this file
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.SAT

open Cost

/-- Boolean formulas over input bits. -/
inductive Fml where
  | inp (i : ℕ)
  | const (b : Bool)
  | and (f g : Fml)
  | or (f g : Fml)
  | not (f : Fml)
  deriving DecidableEq, Repr, Inhabited

namespace Fml

/-- The value of a formula on the input bits `x`. -/
def eval (x : ℕ → Bool) : Fml → Bool
  | inp i => x i
  | const b => b
  | and f g => f.eval x && g.eval x
  | or f g => f.eval x || g.eval x
  | not f => !f.eval x

/-- The number of nodes: the number of gates of the circuit. -/
def size : Fml → ℕ
  | inp _ => 1
  | const _ => 1
  | and f g => f.size + g.size + 1
  | or f g => f.size + g.size + 1
  | not f => f.size + 1

/-- Every input bit read is below `n`. -/
def InputsLt (n : ℕ) : Fml → Prop
  | inp i => i < n
  | const _ => True
  | and f g => f.InputsLt n ∧ g.InputsLt n
  | or f g => f.InputsLt n ∧ g.InputsLt n
  | not f => f.InputsLt n

/-! ## Formulas as data: the post-order serialization -/

/-- The nodes of the post-order (reverse Polish) serialization of a formula. -/
inductive Node where
  | inp (i : ℕ)
  | const (b : Bool)
  | and
  | or
  | not
  deriving DecidableEq, Repr, Inhabited

namespace Node

/-- Nodes as data: a unary tag and the payload. -/
def toData : Node → Data
  | inp i => .cons (.ofNat 0) (encode i)
  | const b => .cons (.ofNat 1) (encode b)
  | and => .cons (.ofNat 2) .nil
  | or => .cons (.ofNat 3) .nil
  | not => .cons (.ofNat 4) .nil

/-- Decoding nodes. -/
def ofData? : Data → Option Node
  | .cons .nil p => (decode p : Option ℕ).map inp
  | .cons (.cons .nil .nil) p => (decode p : Option Bool).map const
  | .cons (.cons .nil (.cons .nil .nil)) .nil => some and
  | .cons (.cons .nil (.cons .nil (.cons .nil .nil))) .nil => some or
  | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))) .nil => some not
  | _ => none

theorem ofData?_toData : ∀ nd : Node, ofData? nd.toData = some nd
  | inp i => by simp [toData, ofData?, Data.ofNat, SizedEncoding.decode_encode]
  | const b => by cases b <;> rfl
  | and => rfl
  | or => rfl
  | not => rfl

instance : SizedEncoding Node where
  encode := toData
  decode := ofData?
  decode_encode := ofData?_toData

theorem encode_inp (i : ℕ) : (encode (inp i) : Data) = .cons (.ofNat 0) (encode i) := rfl
theorem encode_const (b : Bool) : (encode (const b) : Data) = .cons (.ofNat 1) (encode b) := rfl

end Node

/-- The post-order serialization of a formula. -/
def rpn : Fml → List Node
  | inp i => [.inp i]
  | const b => [.const b]
  | and f g => f.rpn ++ g.rpn ++ [.and]
  | or f g => f.rpn ++ g.rpn ++ [.or]
  | not f => f.rpn ++ [.not]

@[simp] theorem length_rpn : ∀ f : Fml, f.rpn.length = f.size
  | inp _ => rfl
  | const _ => rfl
  | and f g => by simp [rpn, size, length_rpn f, length_rpn g]; omega
  | or f g => by simp [rpn, size, length_rpn f, length_rpn g]; omega
  | not f => by simp [rpn, size, length_rpn f]

/-- One step of parsing a post-order serialization with a stack of formulas (a malformed
input leaves the stack unchanged). -/
def parseStep (st : List Fml) : Node → List Fml
  | .inp i => inp i :: st
  | .const b => const b :: st
  | .and => match st with
    | g :: f :: st => and f g :: st
    | _ => st
  | .or => match st with
    | g :: f :: st => or f g :: st
    | _ => st
  | .not => match st with
    | f :: st => not f :: st
    | _ => st

theorem foldl_parseStep_rpn : ∀ (f : Fml) (rest : List Node) (st : List Fml),
    (f.rpn ++ rest).foldl parseStep st = rest.foldl parseStep (f :: st)
  | inp _, rest, st => rfl
  | const _, rest, st => rfl
  | and f g, rest, st => by
    simp only [rpn, List.append_assoc]
    rw [foldl_parseStep_rpn f, foldl_parseStep_rpn g]
    rfl
  | or f g, rest, st => by
    simp only [rpn, List.append_assoc]
    rw [foldl_parseStep_rpn f, foldl_parseStep_rpn g]
    rfl
  | not f, rest, st => by
    simp only [rpn, List.append_assoc]
    rw [foldl_parseStep_rpn f]
    rfl

/-- Parsing a post-order serialization. -/
def parse (l : List Node) : Option Fml :=
  match l.foldl parseStep [] with
  | [f] => some f
  | _ => none

theorem parse_rpn (f : Fml) : parse f.rpn = some f := by
  unfold parse
  have := foldl_parseStep_rpn f [] []
  rw [List.append_nil] at this
  rw [this]
  rfl

/-- Formulas encode as their post-order serializations, so that a program builds a formula
by appending lists. -/
instance : SizedEncoding Fml where
  encode f := encode f.rpn
  decode d := (decode d : Option (List Node)).bind parse
  decode_encode f := by simp [SizedEncoding.decode_encode, parse_rpn]

/-- The serialization, as a polynomial-time function (the encoding is the same). -/
noncomputable def rpnF : PolyTimeFun Fml (List Node) := PolyTimeFun.ofEncodeEq rpn fun _ => rfl

@[simp] theorem rpnF_apply (f : Fml) : rpnF f = f.rpn := rfl

/-- The constructors as polynomial-time functions. -/
noncomputable def inpF : PolyTimeFun ℕ Fml :=
  PolyTimeFun.cast (PolyTimeFun.cons (PolyTimeFun.tagged 0 Node.inp Node.encode_inp)
    (PolyTimeFun.const [])) inp fun _ => rfl

noncomputable def constF : PolyTimeFun Bool Fml :=
  PolyTimeFun.cast (PolyTimeFun.cons (PolyTimeFun.tagged 1 Node.const Node.encode_const)
    (PolyTimeFun.const [])) const fun _ => rfl

noncomputable def andF : PolyTimeFun (Fml × Fml) Fml :=
  PolyTimeFun.cast (PolyTimeFun.append.comp
    ((PolyTimeFun.append.comp ((rpnF.comp PolyTimeFun.fst).pair (rpnF.comp PolyTimeFun.snd))).pair
      (PolyTimeFun.const [Node.and])))
    (fun p => and p.1 p.2) fun _ => rfl

noncomputable def orF : PolyTimeFun (Fml × Fml) Fml :=
  PolyTimeFun.cast (PolyTimeFun.append.comp
    ((PolyTimeFun.append.comp ((rpnF.comp PolyTimeFun.fst).pair (rpnF.comp PolyTimeFun.snd))).pair
      (PolyTimeFun.const [Node.or])))
    (fun p => or p.1 p.2) fun _ => rfl

noncomputable def notF : PolyTimeFun Fml Fml :=
  PolyTimeFun.cast (PolyTimeFun.append.comp (rpnF.pair (PolyTimeFun.const [Node.not]))) not
    fun _ => rfl

@[simp] theorem inpF_apply (i : ℕ) : inpF i = inp i := rfl
@[simp] theorem constF_apply (b : Bool) : constF b = const b := rfl
@[simp] theorem andF_apply (p : Fml × Fml) : andF p = and p.1 p.2 := rfl
@[simp] theorem orF_apply (p : Fml × Fml) : orF p = or p.1 p.2 := rfl
@[simp] theorem notF_apply (f : Fml) : notF f = not f := rfl

/-! ## Flattening to a circuit -/

/-- The post-order gate list of a formula whose first gate is at position `base`: the output
gate is the last one, at `base + size - 1`. -/
def flattenAt (base : ℕ) : Fml → List Gate
  | inp i => [.input i]
  | const b => [.const b]
  | and f g => f.flattenAt base ++ g.flattenAt (base + f.size) ++
      [.and (base + f.size - 1) (base + f.size + g.size - 1)]
  | or f g => f.flattenAt base ++ g.flattenAt (base + f.size) ++
      [.or (base + f.size - 1) (base + f.size + g.size - 1)]
  | not f => f.flattenAt base ++ [.not (base + f.size - 1)]

@[simp] theorem length_flattenAt (base : ℕ) : ∀ f : Fml, (f.flattenAt base).length = f.size
  | inp _ => rfl
  | const _ => rfl
  | and f g => by
    simp only [flattenAt, size, List.length_append, List.length_singleton, length_flattenAt base f,
      length_flattenAt _ g]
  | or f g => by
    simp only [flattenAt, size, List.length_append, List.length_singleton, length_flattenAt base f,
      length_flattenAt _ g]
  | not f => by
    simp only [flattenAt, size, List.length_append, List.length_singleton, length_flattenAt base f]

/-- The circuit of a formula on `n` inputs. -/
def toCircuit (n : ℕ) (f : Fml) : Circuit := ⟨n, f.flattenAt 0⟩

@[simp] theorem toCircuit_inputs (n : ℕ) (f : Fml) : (f.toCircuit n).inputs = n := rfl

@[simp] theorem toCircuit_size (n : ℕ) (f : Fml) : (f.toCircuit n).size = f.size := by
  simp [toCircuit, Circuit.size]

/-- The number of references to `u` in a gate list. -/
def refCount (gs : List Gate) (u : ℕ) : ℕ := (gs.map fun g => g.refs.count u).sum

@[simp] theorem refCount_nil (u : ℕ) : refCount [] u = 0 := rfl

@[simp] theorem refCount_append (gs hs : List Gate) (u : ℕ) :
    refCount (gs ++ hs) u = refCount gs u + refCount hs u := by
  simp [refCount]

@[simp] theorem refCount_singleton (g : Gate) (u : ℕ) : refCount [g] u = g.refs.count u := by
  simp [refCount]

/-! ## Evaluation -/

end Fml

end MIPRE.SAT


