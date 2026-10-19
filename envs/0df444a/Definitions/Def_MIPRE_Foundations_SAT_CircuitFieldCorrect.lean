-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldCorrect
-- name    : MIPRE_Foundations_SAT_CircuitFieldCorrect
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:32.45903+00:00
-- url     : https://prove2.me/theorems/b59d477c-8115-4a42-a16a-18c47676a597
-- title:
--   Definitions of CircuitFieldCorrect: Correctness of the executable circuit polynomial evaluator
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.CircuitFieldCorrect` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Correctness of the executable circuit polynomial evaluator
--
--   **Definitions** (2): `MIPRE.SAT.Circuit.fieldHistory` (Routing history at a prefix of the actual circuit.); `MIPRE.SAT.Circuit.fieldPrefix`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `readInput_fieldHistory`, `gate_input_width`, `gate_ref_width`, `width_getD`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.CircuitFieldCorrect` (`MIPRE/Foundations/SAT/CircuitFieldCorrect.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 30 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/CircuitFieldCorrect.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitFieldCorrect.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
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
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Theorems.Thm_MIPRE_SAT_Circuit_lastInputValue_range

/-!
# Correctness of the executable circuit polynomial evaluator
-/

namespace MIPRE.SAT.Circuit

open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset

/-- Routing history at a prefix of the actual circuit. -/
def fieldHistory (C : Circuit) (w : List BitStr) (k : ℕ) : List (Gate × BitStr) :=
  (List.range k).map (fun j => (C.gates.getD j (.const false), w.getD j []))

def fieldPrefix (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) : FieldState :=
  (C.fieldHistory w k).foldl fieldStep ((p, x, w, []), oneBits p)

theorem readInput_fieldHistory (C : Circuit) (p : BitStr) (x w : List BitStr) (k i : ℕ) :
    readInput (p, x, w, C.fieldHistory w k) i =
      Sum.elim (fun j => x.getD j []) (fun j => w.getD j []) (C.inputRef k i) :=
  lastInputValue_range C k i (fun j => x.getD j []) (fun j => w.getD j [])

theorem width_getD (p : BitStr) (l : List BitStr)
    (h : ∀ b ∈ l, b.length = p.length) (i : ℕ) (hi : i < l.length) :
    (l.getD i []).length = p.length := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h _ (List.getElem_mem hi)

theorem gate_ref_width (C : Circuit) (hC : C.WellFormed) (p : BitStr)
    (w : List BitStr) (hwlen : C.size ≤ w.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    ∀ j ∈ (C.gates.getD k (.const false)).refs, (w.getD j []).length = p.length := by
  intro j hj
  have hr := hC.refs_lt k hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
  exact width_getD p w hw j (lt_of_lt_of_le (lt_trans (hr j hj) hk) hwlen)

theorem gate_input_width (C : Circuit) (hC : C.WellFormed) (p : BitStr)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    ∀ i, C.gates.getD k (.const false) = .input i →
      (readInput (p, x, w, C.fieldHistory w k) i).length = p.length := by
  intro i hi
  rw [readInput_fieldHistory]
  rcases C.inputRef_cases k i with he | ⟨u, hu, he, _⟩
  · rw [he]
    have himem : Gate.input i ∈ C.gates := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hi
      exact hi ▸ List.getElem_mem hk
    exact width_getD p x hx i ((hC.inputs_lt i himem).trans_le hxlen)
  · rw [he]
    exact width_getD p w hw u ((hu.trans hk).trans_le hwlen)

variable {F : Type*} [Field F] [CharP F 2]

end MIPRE.SAT.Circuit


