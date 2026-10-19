-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
-- name    : MIPRE_Foundations_SAT_CircuitFieldEval
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:04:37.616829+00:00
-- url     : https://prove2.me/theorems/e7063b75-0223-4828-8c6e-68b9c47d7d70
-- title:
--   Definitions of CircuitFieldEval: Effective evaluation of the routed circuit polynomial The evaluator multiplies the gate-consistency factors, retaining…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.CircuitFieldEval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Effective evaluation of the routed circuit polynomial. The evaluator multiplies the gate-consistency factors, retaining preceding input-copy values for routing. It works directly on coefficient vectors and never expands the polynomial into monomials.
--
--   **Definitions** (10): `MIPRE.SAT.Circuit.FieldState`; `MIPRE.SAT.Circuit.circuitBits` (The complete circuit polynomial evaluator on coefficient vectors.); `MIPRE.SAT.Circuit.circuitBitsProg` (Uniform polynomial-time evaluation of the routed circuit polynomial.); `MIPRE.SAT.Circuit.factorBits` (One gate-consistency factor, with its claimed gate value.); `MIPRE.SAT.Circuit.factorBitsProg`; `MIPRE.SAT.Circuit.fieldScanProg` (The scan is an ambient polynomial-time program even on malformed inputs.); `MIPRE.SAT.Circuit.fieldStep` (Append the gate to the routing history and multiply its consistency factor.); `MIPRE.SAT.Circuit.fieldStepProg`; `MIPRE.SAT.Circuit.gatePairs` (Pair each actual gate with its supplied coordinate; short malformed coordinate arrays use the empty vector.); `MIPRE.SAT.Circuit.gatePairsProg`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `circuitBitsProg_apply`, `factorBitsProg_apply`, `fieldScanProg_apply`, `fieldStepProg_apply`, `fieldStep_width_le`, `fold_fieldStep`, `gatePairsProg_apply`, `fieldStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.CircuitFieldEval` (`MIPRE/Foundations/SAT/CircuitFieldEval.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 27 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/CircuitFieldEval.lean; blueprint lem:pcp-circuit-evaluator

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitFieldEval.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-!
# Effective evaluation of the routed circuit polynomial

The evaluator multiplies the gate-consistency factors, retaining preceding
input-copy values for routing. It works directly on coefficient vectors and
never expands the polynomial into monomials.
-/

namespace MIPRE.SAT.Circuit

open Cost LowDegree LowDegree.BinaryPolynomial

/-- One gate-consistency factor, with its claimed gate value. -/
def factorBits (e : FieldEnv) (a : Gate × BitStr) : BitStr :=
  xorBits (xorBits (oneBits e.1) a.2) (gateBits e.1 (readInput e) e.2.2.1 a.1)

abbrev FieldState := FieldEnv × BitStr

/-- Append the gate to the routing history and multiply its consistency factor. -/
def fieldStep (s : FieldState) (a : Gate × BitStr) : FieldState :=
  ((s.1.1, s.1.2.1, s.1.2.2.1, s.1.2.2.2 ++ [a]),
    mulReduce s.1.1 s.2 (factorBits s.1 a))

theorem fieldStep_width_le (s : FieldState) (a : Gate × BitStr) :
    (fieldStep s a).2.length ≤ s.2.length := length_mulReduce_le _ _ _

/-- The fold retains the modulus and coordinates, stores only the scanned
history, and never increases its accumulator's coefficient width. -/
theorem fold_fieldStep (l : List (Gate × BitStr)) (s : FieldState) :
    (l.foldl fieldStep s).1 =
      (s.1.1, s.1.2.1, s.1.2.2.1, s.1.2.2.2 ++ l) ∧
    (l.foldl fieldStep s).2.length ≤ s.2.length := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    obtain ⟨he, hw⟩ := ih (fieldStep s a)
    constructor
    · simpa [fieldStep, List.append_assoc] using he
    · exact hw.trans (fieldStep_width_le s a)

/-- Pair each actual gate with its supplied coordinate; short malformed
coordinate arrays use the empty vector. -/
def gatePairs (gs : List Gate) (w : List BitStr) : List (Gate × BitStr) :=
  (List.range gs.length).map (fun j => (gs.getD j (.const false), w.getD j []))

/-- The complete circuit polynomial evaluator on coefficient vectors. -/
def circuitBits (p : BitStr) (x w : List BitStr) (gs : List Gate) : BitStr :=
  mulReduce p
    ((gatePairs gs w).foldl fieldStep ((p, x, w, []), oneBits p)).2
    (w.getD (gs.length - 1) [])

section Programs

open Cost.PolyTimeFun Polynomial

noncomputable def factorBitsProg : PolyTimeFun (FieldEnv × (Gate × BitStr)) BitStr :=
  xorBitsProg.comp
    ((xorBitsProg.comp ((oneBitsProg.comp (fst.comp fst)).pair (snd.comp snd))).pair
      (gateBitsProg.comp (fst.pair (fst.comp snd))))

@[simp] theorem factorBitsProg_apply (e : FieldEnv) (a : Gate × BitStr) :
    factorBitsProg (e, a) = factorBits e a := rfl

noncomputable def fieldStepProg : PolyTimeFun (FieldState × (Gate × BitStr)) FieldState :=
  let e : PolyTimeFun (FieldState × (Gate × BitStr)) FieldEnv := fst.comp fst
  let p := fst.comp e
  let x := fst.comp (snd.comp e)
  let w := fst.comp (snd.comp (snd.comp e))
  let history := snd.comp (snd.comp (snd.comp e))
  (p.pair (x.pair (w.pair (append.comp (history.pair (cons snd (const []))))))).pair
    (mulReduceProg.comp (p.pair ((snd.comp fst).pair
      (factorBitsProg.comp (e.pair snd)))))

@[simp] theorem fieldStepProg_apply (s : FieldState) (a : Gate × BitStr) :
    fieldStepProg (s, a) = fieldStep s a := rfl

theorem fieldStep_bounded : FoldBounded fieldStepProg (5 * X + 5) := by
  intro l s pre post hl
  change esize (pre.foldl fieldStep s) ≤ _
  obtain ⟨he, hw⟩ := fold_fieldStep pre s
  have ha := esize_bitStr_le (pre.foldl fieldStep s).2
  have hi := length_le_esize_list s.2
  have hh := esize_list_append s.1.2.2.2 pre
  have hp := esize_list_append pre post
  rw [← hl] at hp
  have hs : esize s =
      (esize s.1.1 + (esize s.1.2.1 + (esize s.1.2.2.1 + esize s.1.2.2.2 + 1) + 1) + 1) +
        esize s.2 + 1 := rfl
  rw [esize_prod, he]
  simp only [esize_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- The scan is an ambient polynomial-time program even on malformed inputs. -/
noncomputable def fieldScanProg : PolyTimeFun (List (Gate × BitStr) × FieldState) FieldState :=
  foldl fieldStepProg (5 * X + 5) fieldStep_bounded

@[simp] theorem fieldScanProg_apply (l : List (Gate × BitStr)) (s : FieldState) :
    fieldScanProg (l, s) = l.foldl fieldStep s := rfl

noncomputable def gatePairsProg : PolyTimeFun (List Gate × List BitStr) (List (Gate × BitStr)) :=
  let item : PolyTimeFun (ℕ × (List Gate × List BitStr)) (Gate × BitStr) :=
    ((ArrayProg.getD (.const false)).comp (fst.pair (fst.comp snd))).pair
      ((ArrayProg.getD []).comp (fst.pair (snd.comp snd)))
  congr ((mapWith item).comp
    ((range'P.comp ((const 0).pair (length.comp fst))).pair (PolyTimeFun.id _)))
    (fun p => gatePairs p.1 p.2) (by
      intro p
      simp only [comp_apply, mapWith_apply, pair_apply, range'P_apply, const_apply,
        length_apply, fst_apply, length_unary, id_apply, item, ArrayProg.getD_apply,
        snd_apply, gatePairs, List.range_eq_range'])

@[simp] theorem gatePairsProg_apply (p : List Gate × List BitStr) :
    gatePairsProg p = gatePairs p.1 p.2 := rfl

/-- Uniform polynomial-time evaluation of the routed circuit polynomial.
The input contains the modulus, external coordinates, gate coordinates, and gates. -/
noncomputable def circuitBitsProg :
    PolyTimeFun (BitStr × List BitStr × List BitStr × List Gate) BitStr :=
  let p : PolyTimeFun (BitStr × List BitStr × List BitStr × List Gate) BitStr := fst
  let x := fst.comp snd
  let w := fst.comp (snd.comp snd)
  let gs := snd.comp (snd.comp snd)
  let pairs := gatePairsProg.comp (gs.pair w)
  let state := (p.pair (x.pair (w.pair (const [])))).pair (oneBitsProg.comp p)
  let acc := snd.comp (fieldScanProg.comp (pairs.pair state))
  let last := unaryToBin.comp (tail.comp (length.comp gs))
  congr (mulReduceProg.comp (p.pair (acc.pair ((ArrayProg.getD []).comp (last.pair w)))))
    (fun a => circuitBits a.1 a.2.1 a.2.2.1 a.2.2.2) (by
      intro a
      simp only [p, x, w, gs, pairs, state, acc, last, comp_apply, mulReduceProg_apply,
        pair_apply, fst_apply, snd_apply, fieldScanProg_apply, gatePairsProg_apply,
        const_apply, oneBitsProg_apply, ArrayProg.getD_apply, unaryToBin_apply,
        tail_apply, length_apply, List.length_tail, length_unary, circuitBits])

@[simp] theorem circuitBitsProg_apply (p : BitStr) (x w : List BitStr) (gs : List Gate) :
    circuitBitsProg (p, x, w, gs) = circuitBits p x w gs := rfl

end Programs

end MIPRE.SAT.Circuit


