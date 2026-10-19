-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
-- name    : MIPRE_Foundations_SAT_InputRoutingProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:27.887979+00:00
-- url     : https://prove2.me/theorems/c1a7497a-9a18-4ff0-929d-08ea71bb711c
-- title:
--   Definitions of InputRoutingProg: Effective lookup of the preceding input copy The field evaluator scans the already supplied gate/value pairs
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.InputRoutingProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Effective lookup of the preceding input copy. The field evaluator scans the already supplied gate/value pairs. A read of input `i` uses the last value attached to an earlier input gate for `i`, or the external input value if there is no such gate. Binary indices are compared directly; malformed large indices never cause unary expansion.
--
--   **Definitions** (5): `MIPRE.SAT.Circuit.lastInputValue` (Last supplied value of an input gate for `i`, with a supplied initial value.); `MIPRE.SAT.Circuit.lastInputValueProg` (The last-input-value scan, with an ambient polynomial running-time proof.); `MIPRE.SAT.Circuit.matchesInputProg` (Test whether a gate reads the specified external input.); `_private.MIPRE.Foundations.SAT.InputRoutingProg.0.MIPRE.SAT.Circuit.inputStep`; `_private.MIPRE.Foundations.SAT.InputRoutingProg.0.MIPRE.SAT.Circuit.inputStepProg`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `lastInputValueProg_apply`, `lastInputValue_append`, `matchesInputProg_apply`, `fold_inputStep`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.InputRoutingProg` (`MIPRE/Foundations/SAT/InputRoutingProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 20 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/InputRoutingProg.lean; blueprint lem:pcp-circuit-evaluator

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/InputRoutingProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
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

/-!
# Effective lookup of the preceding input copy

The field evaluator scans the already supplied gate/value pairs. A read of
input `i` uses the last value attached to an earlier input gate for `i`, or
the external input value if there is no such gate. Binary indices are compared
directly; malformed large indices never cause unary expansion.
-/

namespace MIPRE.SAT.Circuit

open Cost Cost.PolyTimeFun Polynomial

/-- Test whether a gate reads the specified external input. -/
noncomputable def matchesInputProg : PolyTimeFun (ℕ × Gate) Bool :=
  congr (MIPRE.SAT.PolyTimeFun.casesGate ArrayProg.eqNat
    (const false) (const false) (const false) (const false))
    (fun p => decide (p.2 = .input p.1)) (by
      rintro ⟨i, g⟩
      cases g with
      | input j => change decide (i = j) = decide (Gate.input j = Gate.input i); simp [eq_comm]
      | const b => rfl
      | and u v => rfl
      | or u v => rfl
      | not u => rfl)

@[simp] theorem matchesInputProg_apply (p : ℕ × Gate) :
    matchesInputProg p = decide (p.2 = .input p.1) := rfl

variable {α : Type*} [SizedEncoding α]

/-- Last supplied value of an input gate for `i`, with a supplied initial value. -/
def lastInputValue (l : List (Gate × α)) (i : ℕ) (initial : α) : α :=
  l.foldl (fun acc p => if p.1 = .input i then p.2 else acc) initial

@[simp] theorem lastInputValue_append (l r : List (Gate × α)) (i : ℕ) (a : α) :
    lastInputValue (l ++ r) i a = lastInputValue r i (lastInputValue l i a) := by
  exact List.foldl_append

def inputStep (s : ℕ × α) (p : Gate × α) : ℕ × α :=
  (s.1, if p.1 = .input s.1 then p.2 else s.2)

noncomputable def inputStepProg : PolyTimeFun ((ℕ × α) × (Gate × α)) (ℕ × α) :=
  congr ((fst.comp fst).pair
    (ite (ap₂ matchesInputProg (fst.comp fst) (fst.comp snd)) (snd.comp snd) (snd.comp fst)))
    (fun p => inputStep p.1 p.2) (by intro p; simp [inputStep])

theorem fold_inputStep (l : List (Gate × α)) (i : ℕ) (initial : α) :
    l.foldl inputStep (i, initial) = (i, lastInputValue l i initial) := by
  induction l generalizing initial with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons, inputStep, ih, lastInputValue]

/-- The last-input-value scan, with an ambient polynomial running-time proof. -/
noncomputable def lastInputValueProg : PolyTimeFun ((ℕ × α) × List (Gate × α)) α :=
  let scan := foldlAdd inputStepProg X (by
    rintro ⟨i, a⟩ ⟨g, b⟩
    change esize (inputStep (i, a) (g, b)) ≤ _
    simp only [inputStep, esize_prod, Polynomial.eval_X]
    split_ifs <;> omega)
  congr (snd.comp (scan.comp (snd.pair fst)))
    (fun p => lastInputValue p.2 p.1.1 p.1.2) (by
      rintro ⟨⟨i, a⟩, l⟩
      change (l.foldl inputStep (i, a)).2 = _
      rw [fold_inputStep])

@[simp] theorem lastInputValueProg_apply (p : (ℕ × α) × List (Gate × α)) :
    lastInputValueProg p = lastInputValue p.2 p.1.1 p.1.2 := rfl

end MIPRE.SAT.Circuit


