-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
-- name    : MIPRE_Foundations_LowDegree_BinaryTrace
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:27.636284+00:00
-- url     : https://prove2.me/theorems/2219bbcb-5d49-4f1e-b19a-35f0313f0c1b
-- title:
--   Definitions of BinaryTrace: Effective Frobenius iteration and trace A fixed-width loop squares its current field element and adds it to a trace…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryTrace` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Effective Frobenius iteration and trace. A fixed-width loop squares its current field element and adds it to a trace accumulator. The loop count is unary, so `k` Frobenius operations take `poly(k)` time even though the represented exponent is `2^k`.
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryPolynomial.frobeniusTrace` (Both the final Frobenius iterate and the sum of the preceding iterates.); `MIPRE.LowDegree.BinaryPolynomial.frobeniusTraceProg` (Uniform computation of Frobenius iteration and the associated trace sum.); `MIPRE.LowDegree.BinaryPolynomial.traceStep`; `_private.MIPRE.Foundations.LowDegree.BinaryTrace.0.MIPRE.LowDegree.BinaryPolynomial.traceStepProg`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fold_traceStep_width`, `frobeniusTraceProg_apply`, `traceStep_width`, `traceStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryTrace` (`MIPRE/Foundations/LowDegree/BinaryTrace.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryTrace.lean; blueprint lem:effective-field-inverse-trace

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryTrace.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-!
# Effective Frobenius iteration and trace

A fixed-width loop squares its current field element and adds it to a trace
accumulator. The loop count is unary, so `k` Frobenius operations take `poly(k)`
time even though the represented exponent is `2^k`.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

def traceStep (s : PowerState) (_ : Unit) : PowerState :=
  (s.1, mulReduce s.1 s.2.1 s.2.1, xorBits s.2.2 s.2.1)

theorem traceStep_width (s : PowerState) (u : Unit) :
    (traceStep s u).1 = s.1 ∧
    (traceStep s u).2.1.length ≤ s.2.1.length ∧
    (traceStep s u).2.2.length ≤ s.2.2.length :=
  ⟨rfl, length_mulReduce_le _ _ _, by
    change (xorBits s.2.2 s.2.1).length ≤ _
    rw [length_xorBits]
    exact min_le_left _ _⟩

theorem fold_traceStep_width (u : Unary) (s : PowerState) :
    (u.foldl traceStep s).1 = s.1 ∧
    (u.foldl traceStep s).2.1.length ≤ s.2.1.length ∧
    (u.foldl traceStep s).2.2.length ≤ s.2.2.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, le_rfl, le_rfl⟩
  | cons b u ih =>
    obtain ⟨hp, ha, hc⟩ := ih (traceStep s b)
    obtain ⟨_, ha', hc'⟩ := traceStep_width s b
    exact ⟨hp, ha.trans ha', hc.trans hc'⟩

/-- Both the final Frobenius iterate and the sum of the preceding iterates. -/
def frobeniusTrace (p a : BitStr) (u : Unary) : BitStr × BitStr :=
  (u.foldl traceStep (p, a, zeroBits p)).2

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def traceStepProg : PolyTimeFun (PowerState × Unit) PowerState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let c := snd.comp (snd.comp fst)
  p.pair ((mulReduceProg.comp (p.pair (a.pair a))).pair (xorBitsProg.comp (c.pair a)))

theorem traceStep_bounded : FoldBounded traceStepProg (9 * X + 9) := by
  intro l s pre post _
  change esize (pre.foldl traceStep s) ≤ _
  obtain ⟨hp, ha, hc⟩ := fold_traceStep_width pre s
  have ha0 := length_le_esize_list s.2.1
  have hc0 := length_le_esize_list s.2.2
  have hsa := esize_bitStr_le (pre.foldl traceStep s).2.1
  have hsc := esize_bitStr_le (pre.foldl traceStep s).2.2
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  rw [esize_prod, esize_prod, hp]
  grw [hsa, hsc, ha, hc, ha0, hc0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, esize_prod]
  omega

/-- Uniform computation of Frobenius iteration and the associated trace sum. -/
noncomputable def frobeniusTraceProg :
    PolyTimeFun (BitStr × BitStr × Unary) (BitStr × BitStr) :=
  congr (snd.comp ((foldl traceStepProg (9 * X + 9) traceStep_bounded).comp
    ((snd.comp snd).pair (fst.pair ((fst.comp snd).pair (zeroBitsProg.comp fst))))))
    (fun p => frobeniusTrace p.1 p.2.1 p.2.2) (by intro p; rfl)

@[simp] theorem frobeniusTraceProg_apply (p a : BitStr) (u : Unary) :
    frobeniusTraceProg (p, a, u) = frobeniusTrace p a u := rfl

end MIPRE.LowDegree.BinaryPolynomial


