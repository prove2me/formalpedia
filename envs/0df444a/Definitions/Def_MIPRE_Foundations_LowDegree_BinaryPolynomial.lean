-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
-- name    : MIPRE_Foundations_LowDegree_BinaryPolynomial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:48.361422+00:00
-- url     : https://prove2.me/theorems/c467d818-559b-42c6-8944-6944cf235c4a
-- title:
--   Definitions of BinaryPolynomial: Binary polynomial arithmetic on coefficient lists Coefficient lists are little-endian
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryPolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Binary polynomial arithmetic on coefficient lists. Coefficient lists are little-endian. XOR implements addition, and multiplication by the indeterminate is reduced using the lower coefficients of a monic modulus. The semantic lemmas work in every characteristic-two commutative ring containing a root of that modulus; the programs are uniform in the coefficient lists.
--
--   **Definitions** (16): `MIPRE.LowDegree.BinaryPolynomial.evalBits` (Evaluate a little-endian binary coefficient list by Horner's rule.); `MIPRE.LowDegree.BinaryPolynomial.mulReduce` (Horner multiplication, reducing after every shift.); `MIPRE.LowDegree.BinaryPolynomial.mulReduceProg` (Uniform polynomial-time multiplication modulo a binary monic polynomial.); `MIPRE.LowDegree.BinaryPolynomial.shiftLow` (Shift by one coefficient and discard the new highest coefficient.); `MIPRE.LowDegree.BinaryPolynomial.shiftReduce` (Multiply by the indeterminate modulo `X^k + p`, with `p` represented by exactly `k` lower coefficients.); `MIPRE.LowDegree.BinaryPolynomial.shiftReduceProg` (Uniform polynomial-time multiplication by the indeterminate modulo a binary monic polynomial.); `MIPRE.LowDegree.BinaryPolynomial.takeBitsProg` (Take a unary-specified number of coefficients in polynomial time.); `MIPRE.LowDegree.BinaryPolynomial.xorBitProg` (XOR of two bits, as an ambient program.); `MIPRE.LowDegree.BinaryPolynomial.xorBits` (Fixed-width XOR, used only with equal-width operands in correctness lemmas.); `MIPRE.LowDegree.BinaryPolynomial.xorBitsProg` (Uniform polynomial-time addition of fixed-width coefficient vectors.); `_private.MIPRE.Foundations.LowDegree.BinaryPolynomial.0.MIPRE.LowDegree.BinaryPolynomial.MulState`; `_private.MIPRE.Foundations.LowDegree.BinaryPolynomial.0.MIPRE.LowDegree.BinaryPolynomial.headProg`; and 1 more.
--
--   **Embedded lemmas** (15): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `evalBits_cons`, `evalBits_nil`, `evalBits_zero`, `length_shiftLow`, `length_shiftReduce_le`, `length_xorBits`, `mulReduceProg_apply`, `shiftReduceProg_apply`, `takeBitsProg_apply`, `xorBitsProg_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryPolynomial` (`MIPRE/Foundations/LowDegree/BinaryPolynomial.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 8 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryPolynomial.lean; blueprint lem:effective-binary-field-arithmetic

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPolynomial.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation

/-!
# Binary polynomial arithmetic on coefficient lists

Coefficient lists are little-endian. XOR implements addition, and multiplication
by the indeterminate is reduced using the lower coefficients of a monic modulus.
The semantic lemmas work in every characteristic-two commutative ring containing
a root of that modulus; the programs are uniform in the coefficient lists.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost

variable {R : Type*} [CommRing R]

/-- Evaluate a little-endian binary coefficient list by Horner's rule. -/
def evalBits (z : R) : BitStr → R
  | [] => 0
  | b :: l => ofBool b + z * evalBits z l

@[simp] theorem evalBits_nil (z : R) : evalBits z [] = 0 := rfl

@[simp] theorem evalBits_cons (z : R) (b : Bool) (l : BitStr) :
    evalBits z (b :: l) = ofBool b + z * evalBits z l := rfl

@[simp] theorem evalBits_zero (z : R) (n : ℕ) :
    evalBits z (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ofBool, ih]

/-- Fixed-width XOR, used only with equal-width operands in correctness lemmas. -/
def xorBits (a b : BitStr) : BitStr := List.zipWith Bool.xor a b

@[simp] theorem length_xorBits (a b : BitStr) :
    (xorBits a b).length = min a.length b.length := by simp [xorBits]

/-- Shift by one coefficient and discard the new highest coefficient. -/
def shiftLow (a : BitStr) : BitStr := (false :: a).dropLast

/-- Multiply by the indeterminate modulo `X^k + p`, with `p` represented by
exactly `k` lower coefficients. -/
def shiftReduce (p a : BitStr) : BitStr :=
  if a.getLastD false then xorBits (shiftLow a) p else shiftLow a

@[simp] theorem length_shiftLow (a : BitStr) : (shiftLow a).length = a.length := by
  simp [shiftLow]

theorem length_shiftReduce_le (p a : BitStr) : (shiftReduce p a).length ≤ a.length := by
  unfold shiftReduce
  split <;> simp

/-- Horner multiplication, reducing after every shift. -/
def mulReduce (p a b : BitStr) : BitStr :=
  b.foldr (fun bit acc =>
    if bit then xorBits (shiftReduce p acc) a else shiftReduce p acc)
    (List.replicate a.length false)

section Programs

open PolyTimeFun

/-- Take a unary-specified number of coefficients in polynomial time. -/
noncomputable def takeBitsProg : PolyTimeFun (Unary × BitStr) BitStr :=
  PolyTimeFun.congr ((map snd).comp zip) (fun p => p.2.take p.1.length) (by
    rintro ⟨u, l⟩
    change (u.zip l).map Prod.snd = l.take u.length
    induction u generalizing l with
    | nil => simp
    | cons x u ih => cases l <;> simp [ih])

@[simp] theorem takeBitsProg_apply (p : Unary × BitStr) :
    takeBitsProg p = p.2.take p.1.length := rfl

/-- XOR of two bits, as an ambient program. -/
noncomputable def xorBitProg : PolyTimeFun (Bool × Bool) Bool :=
  PolyTimeFun.congr (ite fst (ite snd (const false) (const true)) snd) (fun p => p.1 ^^ p.2)
    (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)

/-- Uniform polynomial-time addition of fixed-width coefficient vectors. -/
noncomputable def xorBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  PolyTimeFun.congr ((map xorBitProg).comp zip) (fun p => xorBits p.1 p.2) (by
    intro p
    change (p.1.zip p.2).map (fun q => q.1 ^^ q.2) = List.zipWith Bool.xor p.1 p.2
    exact List.map_zip_eq_zipWith)

@[simp] theorem xorBitsProg_apply (p : BitStr × BitStr) :
    xorBitsProg p = xorBits p.1 p.2 := rfl

noncomputable def headProg : PolyTimeFun BitStr Bool :=
  PolyTimeFun.congr
    ((casesList (const false) (fst.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    (fun a => a.headD false) (by intro a; cases a <;> rfl)

noncomputable def tailProg : PolyTimeFun BitStr BitStr :=
  PolyTimeFun.congr
    ((casesList (const []) (snd.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.tail (by intro a; cases a <;> rfl)

noncomputable def shiftLowProg : PolyTimeFun BitStr BitStr :=
  PolyTimeFun.congr
    (reverse.comp (tailProg.comp (reverse.comp (cons (const false) (PolyTimeFun.id _)))))
    shiftLow (by
      intro a
      change ((false :: a).reverse.tail).reverse = (false :: a).dropLast
      rw [List.tail_reverse, List.reverse_reverse])

/-- Uniform polynomial-time multiplication by the indeterminate modulo a binary
monic polynomial. The input is the lower-coefficient vector and the operand. -/
noncomputable def shiftReduceProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  PolyTimeFun.congr
    (ite (headProg.comp (reverse.comp snd))
      (xorBitsProg.comp ((shiftLowProg.comp snd).pair fst)) (shiftLowProg.comp snd))
    (fun p => shiftReduce p.1 p.2) (by
      intro p
      change (if p.2.reverse.headD false then xorBits (shiftLow p.2) p.1 else shiftLow p.2) = _
      simp only [List.headD_eq_head?_getD, List.head?_reverse, ← List.getLastD_eq_getLast?]
      rfl)

@[simp] theorem shiftReduceProg_apply (p : BitStr × BitStr) :
    shiftReduceProg p = shiftReduce p.1 p.2 := rfl

abbrev MulState := BitStr × BitStr × BitStr

def mulStep (s : MulState) (bit : Bool) : MulState :=
  (s.1, s.2.1, if bit then xorBits (shiftReduce s.1 s.2.2) s.2.1
    else shiftReduce s.1 s.2.2)

noncomputable def mulStepProg : PolyTimeFun (MulState × Bool) MulState :=
  let p := fst.comp fst
  let a := fst.comp (snd.comp fst)
  let acc := snd.comp (snd.comp fst)
  let shifted := shiftReduceProg.comp (p.pair acc)
  p.pair (a.pair (ite snd (xorBitsProg.comp (shifted.pair a)) shifted))

theorem mulStepProg_apply (s : MulState) (bit : Bool) :
    mulStepProg (s, bit) = mulStep s bit := rfl

theorem mulStep_length (s : MulState) (bit : Bool) :
    (mulStep s bit).2.2.length ≤ s.2.2.length := by
  unfold mulStep
  split
  · change (xorBits (shiftReduce s.1 s.2.2) s.2.1).length ≤ _
    rw [length_xorBits]
    exact (min_le_left _ _).trans (length_shiftReduce_le _ _)
  · exact length_shiftReduce_le _ _

theorem foldl_mulStep (l : BitStr) (s : MulState) :
    (l.foldl mulStep s).1 = s.1 ∧
      (l.foldl mulStep s).2.1 = s.2.1 ∧
      (l.foldl mulStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, le_rfl⟩
  | cons bit l ih =>
    obtain ⟨hp, ha, hacc⟩ := ih (mulStep s bit)
    exact ⟨hp, ha, hacc.trans (mulStep_length s bit)⟩

theorem mulStepProg_bounded :
    PolyTimeFun.FoldBounded mulStepProg (4 * Polynomial.X + 4) := by
  intro l s pre xs _
  change esize (pre.foldl mulStep s) ≤ _
  obtain ⟨hp, ha, hacc⟩ := foldl_mulStep pre s
  have he := esize_bitStr_le (pre.foldl mulStep s).2.2
  have hinit := length_le_esize_list s.2.2
  change esize (pre.foldl mulStep s).1 +
    (esize (pre.foldl mulStep s).2.1 + esize (pre.foldl mulStep s).2.2 + 1) + 1 ≤ _
  rw [hp, ha]
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

theorem foldr_mulStep (l : BitStr) (p a acc : BitStr) :
    l.foldr (fun bit s => mulStep s bit) (p, a, acc) =
      (p, a, l.foldr (fun bit v =>
        if bit then xorBits (shiftReduce p v) a else shiftReduce p v) acc) := by
  induction l with
  | nil => rfl
  | cons bit l ih => rw [List.foldr_cons, ih]; rfl

/-- Uniform polynomial-time multiplication modulo a binary monic polynomial.
The input carries its lower coefficients and the two operands. -/
noncomputable def mulReduceProg : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  let p : PolyTimeFun MulState BitStr := fst
  let a : PolyTimeFun MulState BitStr := fst.comp snd
  let b : PolyTimeFun MulState BitStr := snd.comp snd
  let zero := replicate.comp ((length.comp a).pair (const false))
  PolyTimeFun.congr
    ((snd.comp snd).comp
      ((foldl mulStepProg (4 * Polynomial.X + 4) mulStepProg_bounded).comp
        ((reverse.comp b).pair (p.pair (a.pair zero)))))
    (fun s => mulReduce s.1 s.2.1 s.2.2) (by
      intro s
      simp only [p, a, b, zero, comp_apply, fst_apply, snd_apply, pair_apply,
        reverse_apply, foldl_apply, replicate_apply, length_apply, length_unary,
        const_apply, mulStepProg_apply]
      change (s.2.2.reverse.foldl mulStep (s.1, s.2.1,
        List.replicate s.2.1.length false)).2.2 = _
      rw [List.foldl_reverse, foldr_mulStep]
      rfl)

@[simp] theorem mulReduceProg_apply (s : BitStr × BitStr × BitStr) :
    mulReduceProg s = mulReduce s.1 s.2.1 s.2.2 := rfl

end Programs

end MIPRE.LowDegree.BinaryPolynomial


