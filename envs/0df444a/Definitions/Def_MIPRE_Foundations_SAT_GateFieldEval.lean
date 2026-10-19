-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
-- name    : MIPRE_Foundations_SAT_GateFieldEval
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:03:56.767639+00:00
-- url     : https://prove2.me/theorems/0be91ecb-1987-4ff6-accb-c0bd73500803
-- title:
--   Definitions of GateFieldEval: Uniform field evaluation of a routed gate Field elements are coefficient vectors modulo a supplied binary monic…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.GateFieldEval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniform field evaluation of a routed gate. Field elements are coefficient vectors modulo a supplied binary monic polynomial. Gate indices stay binary, including on malformed inputs.
--
--   **Definitions** (10): `MIPRE.SAT.Circuit.FieldEnv` (Modulus, external coordinates, gate coordinates, and preceding gate/value pairs.); `MIPRE.SAT.Circuit.gateBits` (Gate arithmetic on coefficient vectors.); `MIPRE.SAT.Circuit.gateBitsProg` (Uniform polynomial-time field evaluation of one routed gate.); `MIPRE.SAT.Circuit.gateValue` (The corresponding field expression in characteristic two.); `MIPRE.SAT.Circuit.oneBits` (Circuit-facing one coefficients, implemented by generic quotient arithmetic.); `MIPRE.SAT.Circuit.oneBitsProg`; `MIPRE.SAT.Circuit.readInput`; `MIPRE.SAT.Circuit.readInputProg`; `MIPRE.SAT.Circuit.zeroBits` (Circuit-facing zero coefficients, implemented by generic quotient arithmetic.); `MIPRE.SAT.Circuit.zeroBitsProg`.
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `evalBits_zeroBits`, `gateBitsProg_apply`, `length_oneBits`, `length_zeroBits`, `oneBitsProg_apply`, `readInputProg_apply`, `zeroBitsProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.GateFieldEval` (`MIPRE/Foundations/SAT/GateFieldEval.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/GateFieldEval.lean; blueprint lem:pcp-circuit-evaluator

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/GateFieldEval.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization

/-!
# Uniform field evaluation of a routed gate

Field elements are coefficient vectors modulo a supplied binary monic
polynomial. Gate indices stay binary, including on malformed inputs.
-/

namespace MIPRE.SAT.Circuit

open Cost LowDegree LowDegree.BinaryPolynomial

-- Retain concrete circuit-facing declarations for downstream compiled consumers.
/-- Circuit-facing zero coefficients, implemented by generic quotient arithmetic. -/
abbrev zeroBits := BinaryPolynomial.zeroBits
/-- Circuit-facing one coefficients, implemented by generic quotient arithmetic. -/
abbrev oneBits := BinaryPolynomial.oneBits
@[simp] theorem length_zeroBits (p : BitStr) : (zeroBits p).length = p.length :=
  BinaryPolynomial.length_zeroBits p
@[simp] theorem length_oneBits (p : BitStr) : (oneBits p).length = p.length :=
  BinaryPolynomial.length_oneBits p
@[simp] theorem evalBits_zeroBits {R : Type*} [CommRing R] (z : R) (p : BitStr) :
    BinaryPolynomial.evalBits z (zeroBits p) = 0 := BinaryPolynomial.evalBits_zeroBits z p
noncomputable abbrev zeroBitsProg : PolyTimeFun BitStr BitStr := BinaryPolynomial.zeroBitsProg
noncomputable abbrev oneBitsProg : PolyTimeFun BitStr BitStr := BinaryPolynomial.oneBitsProg
@[simp] theorem zeroBitsProg_apply (p : BitStr) : zeroBitsProg p = zeroBits p := rfl
@[simp] theorem oneBitsProg_apply (p : BitStr) : oneBitsProg p = oneBits p := rfl

variable {R : Type*} [CommRing R]

/-- Gate arithmetic on coefficient vectors. The input reader is supplied
separately so that the same arithmetic supports the routed copy links. -/
def gateBits (p : BitStr) (x : ℕ → BitStr) (w : List BitStr) : Gate → BitStr
  | .input i => x i
  | .const b => if b then oneBits p else zeroBits p
  | .and u v => mulReduce p (w.getD u []) (w.getD v [])
  | .or u v => xorBits (oneBits p)
      (mulReduce p (xorBits (oneBits p) (w.getD u []))
        (xorBits (oneBits p) (w.getD v [])))
  | .not u => xorBits (oneBits p) (w.getD u [])

/-- The corresponding field expression in characteristic two. -/
def gateValue (x w : ℕ → R) : Gate → R
  | .input i => x i
  | .const b => ofBool b
  | .and u v => w u * w v
  | .or u v => 1 + (1 + w u) * (1 + w v)
  | .not u => 1 + w u

section Programs

open Cost.PolyTimeFun

/-- Modulus, external coordinates, gate coordinates, and preceding gate/value pairs. -/
abbrev FieldEnv := BitStr × List BitStr × List BitStr × List (Gate × BitStr)

def readInput (e : FieldEnv) (i : ℕ) : BitStr :=
  lastInputValue e.2.2.2 i (e.2.1.getD i [])

noncomputable def readInputProg : PolyTimeFun (FieldEnv × ℕ) BitStr :=
  lastInputValueProg.comp
    ((snd.pair ((ArrayProg.getD []).comp (snd.pair (fst.comp (snd.comp fst))))).pair
      ((snd.comp snd).comp (snd.comp fst)))

@[simp] theorem readInputProg_apply (e : FieldEnv) (i : ℕ) :
    readInputProg (e, i) = readInput e i := rfl

/-- Uniform polynomial-time field evaluation of one routed gate. -/
noncomputable def gateBitsProg : PolyTimeFun (FieldEnv × Gate) BitStr :=
  let p : PolyTimeFun FieldEnv BitStr := fst
  let w : PolyTimeFun FieldEnv (List BitStr) := fst.comp (snd.comp snd)
  let one := oneBitsProg.comp p
  let readW : PolyTimeFun (FieldEnv × ℕ) BitStr :=
    (ArrayProg.getD []).comp (snd.pair (w.comp fst))
  let a : PolyTimeFun (FieldEnv × (ℕ × ℕ)) BitStr := readW.comp (fst.pair (fst.comp snd))
  let b : PolyTimeFun (FieldEnv × (ℕ × ℕ)) BitStr := readW.comp (fst.pair (snd.comp snd))
  let both := mulReduceProg.comp ((p.comp fst).pair (a.pair b))
  let either := xorBitsProg.comp ((one.comp fst).pair
    (mulReduceProg.comp ((p.comp fst).pair
      ((xorBitsProg.comp ((one.comp fst).pair a)).pair
        (xorBitsProg.comp ((one.comp fst).pair b))))))
  congr (MIPRE.SAT.PolyTimeFun.casesGate readInputProg
    (ite snd (one.comp fst) (zeroBitsProg.comp (p.comp fst))) both either
    (xorBitsProg.comp ((one.comp fst).pair readW)))
    (fun eg => gateBits eg.1.1 (readInput eg.1) eg.1.2.2.1 eg.2) (by
      rintro ⟨e, g⟩
      cases g <;> rfl)

@[simp] theorem gateBitsProg_apply (e : FieldEnv) (g : Gate) :
    gateBitsProg (e, g) = gateBits e.1 (readInput e) e.2.2.1 g := rfl

end Programs

end MIPRE.SAT.Circuit


