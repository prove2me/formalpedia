-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
-- name    : MIPRE_Foundations_LowDegree_BinaryDivision
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:30.415577+00:00
-- url     : https://prove2.me/theorems/8f7296e7-0635-4a0c-834d-2bb201549018
-- title:
--   Definitions of BinaryDivision: Division by binary monic polynomials The divisor is represented by its lower coefficients `p`; the leading one is…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryDivision` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Division by binary monic polynomials. The divisor is represented by its lower coefficients `p`; the leading one is implicit. Horner long division keeps a fixed-width remainder and records each discarded leading coefficient in the quotient. Division by the constant one has a separate branch. No irreducibility or field structure is assumed.
--
--   **Definitions** (10): `MIPRE.LowDegree.BinaryPolynomial.DivisionState` (Modulus, quotient, and remainder for a Horner division step.); `MIPRE.LowDegree.BinaryPolynomial.divModBits` (Quotient and remainder by the monic polynomial `polyOfBits (p ++ [true])`.); `MIPRE.LowDegree.BinaryPolynomial.divModBitsProg` (Uniform deterministic polynomial-time division by any binary monic polynomial.); `MIPRE.LowDegree.BinaryPolynomial.divisionFold` (Unnormalized Horner division result.); `MIPRE.LowDegree.BinaryPolynomial.divisionFoldProg` (Ambient Horner long division, with one iteration per dividend coefficient.); `MIPRE.LowDegree.BinaryPolynomial.divisionStep` (One input coefficient is appended to the Horner computation.); `_private.MIPRE.Foundations.LowDegree.BinaryDivision.0.MIPRE.LowDegree.BinaryPolynomial.divisionStepProg`; `_private.MIPRE.Foundations.LowDegree.BinaryDivision.0.MIPRE.LowDegree.BinaryPolynomial.headBitProg`; `_private.MIPRE.Foundations.LowDegree.BinaryDivision.0.MIPRE.LowDegree.BinaryPolynomial.isEmptyBitsProg`; `_private.MIPRE.Foundations.LowDegree.BinaryDivision.0.MIPRE.LowDegree.BinaryPolynomial.lastBitProg`.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `divModBitsProg_apply`, `divisionFoldProg_apply`, `divisionStep_width`, `fold_divisionStep_width`, `divisionStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryDivision` (`MIPRE/Foundations/LowDegree/BinaryDivision.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 11 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryDivision.lean; blueprint lem:binary-monic-division

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDivision.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize

/-!
# Division by binary monic polynomials

The divisor is represented by its lower coefficients `p`; the leading one is
implicit. Horner long division keeps a fixed-width remainder and records each
discarded leading coefficient in the quotient. Division by the constant one
has a separate branch. No irreducibility or field structure is assumed.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Modulus, quotient, and remainder for a Horner division step. -/
abbrev DivisionState := BitStr × BitStr × BitStr

/-- One input coefficient is appended to the Horner computation. -/
def divisionStep (s : DivisionState) (b : Bool) : DivisionState :=
  (s.1, s.2.2.getLastD false :: s.2.1,
    if b then xorBits (shiftReduce s.1 s.2.2) (oneBits s.1)
    else shiftReduce s.1 s.2.2)

/-- Quotient width increases once per input coefficient; remainder width cannot grow. -/
theorem divisionStep_width (s : DivisionState) (b : Bool) :
    (divisionStep s b).1 = s.1 ∧
    (divisionStep s b).2.1.length = s.2.1.length + 1 ∧
    (divisionStep s b).2.2.length ≤ s.2.2.length := by
  refine ⟨rfl, rfl, ?_⟩
  cases b
  · exact length_shiftReduce_le _ _
  · change (xorBits (shiftReduce s.1 s.2.2) (oneBits s.1)).length ≤ _
    rw [length_xorBits]
    exact (min_le_left _ _).trans (length_shiftReduce_le _ _)

/-- The width invariant holds for arbitrary initial states, including malformed ones. -/
theorem fold_divisionStep_width (l : BitStr) (s : DivisionState) :
    (l.foldl divisionStep s).1 = s.1 ∧
    (l.foldl divisionStep s).2.1.length = s.2.1.length + l.length ∧
    (l.foldl divisionStep s).2.2.length ≤ s.2.2.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hp, hq, hr⟩ := ih (divisionStep s b)
    obtain ⟨hp', hq', hr'⟩ := divisionStep_width s b
    refine ⟨hp.trans hp', ?_, hr.trans hr'⟩
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- Unnormalized Horner division result. -/
def divisionFold (p a : BitStr) : DivisionState :=
  a.foldr (fun b s => divisionStep s b) (p, [], zeroBits p)

/-- Quotient and remainder by the monic polynomial `polyOfBits (p ++ [true])`.
The degree-zero case divides by one; all outputs are normalized. -/
def divModBits (p a : BitStr) : BitStr × BitStr :=
  if p.isEmpty then (normalizeBits a, [])
  else (normalizeBits (divisionFold p a).2.1, normalizeBits (divisionFold p a).2.2)

noncomputable def headBitProg : PolyTimeFun BitStr Bool :=
  congr ((casesList (const false) (fst.comp snd)).comp
    ((const ()).pair (PolyTimeFun.id _)))
    (fun a => a.headD false) (by intro a; cases a <;> rfl)

noncomputable def lastBitProg : PolyTimeFun BitStr Bool :=
  congr (headBitProg.comp PolyTimeFun.reverse)
    (fun a => a.getLastD false) (by
      intro a
      change a.reverse.headD false = a.getLastD false
      simp only [List.headD_eq_head?_getD, List.head?_reverse, List.getLastD_eq_getLast?])

noncomputable def divisionStepProg : PolyTimeFun (DivisionState × Bool) DivisionState :=
  let p := fst.comp fst
  let q := fst.comp (snd.comp fst)
  let r := snd.comp (snd.comp fst)
  p.pair ((cons (lastBitProg.comp r) q).pair
    (ite snd (xorBitsProg.comp ((shiftReduceProg.comp (p.pair r)).pair (oneBitsProg.comp p)))
      (shiftReduceProg.comp (p.pair r))))

theorem divisionStep_bounded : FoldBounded divisionStepProg (12 * X + 12) := by
  intro l s pre post h
  change esize (pre.foldl divisionStep s) ≤ _
  obtain ⟨hp, hq, hr⟩ := fold_divisionStep_width pre s
  have hqsize := esize_bitStr_le (pre.foldl divisionStep s).2.1
  have hrsize := esize_bitStr_le (pre.foldl divisionStep s).2.2
  have hqin := length_le_esize_list s.2.1
  have hrin := length_le_esize_list s.2.2
  have hpre : pre.length ≤ l.length := by rw [h, List.length_append]; omega
  have hlin := length_le_esize_list l
  have hs : esize s = esize s.1 + (esize s.2.1 + esize s.2.2 + 1) + 1 := rfl
  change esize (pre.foldl divisionStep s).1 +
    (esize (pre.foldl divisionStep s).2.1 + esize (pre.foldl divisionStep s).2.2 + 1) + 1 ≤ _
  rw [hp]
  simp only [esize_prod, hs, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

/-- Ambient Horner long division, with one iteration per dividend coefficient. -/
noncomputable def divisionFoldProg : PolyTimeFun (BitStr × BitStr) DivisionState :=
  congr ((foldl divisionStepProg (12 * X + 12) divisionStep_bounded).comp
    ((PolyTimeFun.reverse.comp snd).pair (fst.pair ((const []).pair (zeroBitsProg.comp fst)))))
    (fun s => divisionFold s.1 s.2) (by
      intro s
      change s.2.reverse.foldl divisionStep (s.1, [], zeroBits s.1) = _
      rw [List.foldl_reverse]
      rfl)

@[simp] theorem divisionFoldProg_apply (p a : BitStr) :
    divisionFoldProg (p, a) = divisionFold p a := rfl

noncomputable def isEmptyBitsProg : PolyTimeFun BitStr Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

/-- Uniform deterministic polynomial-time division by any binary monic polynomial. -/
noncomputable def divModBitsProg : PolyTimeFun (BitStr × BitStr) (BitStr × BitStr) :=
  congr (ite (isEmptyBitsProg.comp fst) ((normalizeBitsProg.comp snd).pair (const []))
    (((normalizeBitsProg.comp (fst.comp snd)).pair (normalizeBitsProg.comp (snd.comp snd))).comp
      divisionFoldProg))
    (fun s => divModBits s.1 s.2) (by intro s; rfl)

@[simp] theorem divModBitsProg_apply (p a : BitStr) :
    divModBitsProg (p, a) = divModBits p a := rfl

end MIPRE.LowDegree.BinaryPolynomial


