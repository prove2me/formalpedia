-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
-- name    : MIPRE_Foundations_LowDegree_BinaryComposedSumProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:12.800974+00:00
-- url     : https://prove2.me/theorems/0bc7238d-2e90-42eb-9ada-13105b5c5e49
-- title:
--   Definitions of BinaryComposedSumProg: Uniform polynomial-time products of Frobenius translates
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryComposedSumProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Uniform polynomial-time products of Frobenius translates
--
--   **Definitions** (9): `MIPRE.LowDegree.BinaryQuotient.NormState` (Modulus, binary polynomial to translate, and accumulating coefficient list.); `MIPRE.LowDegree.BinaryQuotient.composedSumBits` (Binary output of the composed-sum construction for the supplied monic modulus and polynomial.); `MIPRE.LowDegree.BinaryQuotient.composedSumBitsProg` (The composed-sum constructor is polynomial-time on every pair of raw lists.); `MIPRE.LowDegree.BinaryQuotient.normProductBits` (Product of the translates specified by a list of quotient elements.); `MIPRE.LowDegree.BinaryQuotient.normProductBitsProg` (One globally polynomial-time program for a supplied list of polynomial translates.); `MIPRE.LowDegree.BinaryQuotient.normStep` (Multiply the accumulator by one translated copy of the binary polynomial.); `MIPRE.LowDegree.BinaryQuotient.rootBits` (A fixed-width encoding of the canonical quotient root, also valid in degree one.); `MIPRE.LowDegree.BinaryQuotient.rootBitsProg`; `_private.MIPRE.Foundations.LowDegree.BinaryComposedSumProg.0.MIPRE.LowDegree.BinaryQuotient.normStepProg`.
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `composedSumBitsProg_apply`, `length_rootBits`, `normProductBitsProg_apply`, `rootBitsProg_apply`, `fold_normStep_shape`, `fold_normStep_width_le`, `normStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryComposedSumProg` (`MIPRE/Foundations/LowDegree/BinaryComposedSumProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 38 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryComposedSumProg.lean; blueprint lem:binary-coprime-degree-combination

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComposedSumProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_length_mulCoeffLists_le
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_mulCoeffLists_width_le
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_translateBits_width_le

/-! # Uniform polynomial-time products of Frobenius translates -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Modulus, binary polynomial to translate, and accumulating coefficient list. -/
abbrev NormState := BitStr × BitStr × List BitStr

/-- Multiply the accumulator by one translated copy of the binary polynomial. -/
def normStep (s : NormState) (a : BitStr) : NormState :=
  (s.1, s.2.1, mulCoeffLists s.1 (translateBits s.1 a s.2.1) s.2.2)

theorem fold_normStep_shape (pre : List BitStr) (p g : BitStr) (cs : List BitStr) :
    (pre.foldl normStep (p, g, cs)).1 = p ∧ (pre.foldl normStep (p, g, cs)).2.1 = g ∧
      (pre.foldl normStep (p, g, cs)).2.2.length ≤ cs.length + pre.length * g.length := by
  induction pre generalizing cs with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons a pre ih =>
    have h := ih (mulCoeffLists p (translateBits p a g) cs)
    have hl := length_mulCoeffLists_le p (translateBits p a g) cs
    rw [length_translateBits] at hl
    refine ⟨h.1, h.2.1, ?_⟩
    change (pre.foldl normStep (p, g, mulCoeffLists p (translateBits p a g) cs)).2.2.length ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem fold_normStep_width_le (pre : List BitStr) (p g : BitStr) (cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hc : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (pre.foldl normStep (p, g, cs)).2.2, c.length ≤ N := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons a pre ih =>
    apply ih
    exact mulCoeffLists_width_le p _ cs N hp
      (fun c hc' => (translateBits_width_le p a g c hc').trans hp)

variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]

/-- Product of the translates specified by a list of quotient elements. -/
def normProductBits (p g : BitStr) (as : List BitStr) : List BitStr :=
  (as.foldl normStep (p, g, [oneBits p])).2.2

def normStepProg : PolyTimeFun (NormState × BitStr) NormState :=
  let p := fst.comp fst
  let g := fst.comp (snd.comp fst)
  let cs := snd.comp (snd.comp fst)
  congr (p.pair (g.pair (mulCoeffListsProg.comp
    (p.pair ((translateBitsProg.comp (p.pair (snd.pair g))).pair cs)))))
    (fun q => normStep q.1 q.2) (by rintro ⟨⟨p, g, cs⟩, a⟩; rfl)

theorem normStep_bounded :
    FoldBounded normStepProg (30 * X ^ 3 + 30 * X ^ 2 + 30 * X + 30) := by
  intro as s pre post heq
  rcases s with ⟨p, g, cs⟩
  let N := esize (as, p, g, cs)
  have hs : N = esize as + esize p + esize g + esize cs + 3 := by simp [N, esize_prod]; omega
  have hp : p.length ≤ N := by have := length_le_esize_bitStr p; omega
  have hg : g.length ≤ N := by have := length_le_esize_bitStr g; omega
  have hc : cs.length ≤ N := by have := length_le_esize_list cs; omega
  have hpre : pre.length ≤ N := by
    have := length_le_esize_list as
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    omega
  have hshape := fold_normStep_shape pre p g cs
  have hsize := esize_coefficients_le _ N (fold_normStep_width_le pre p g cs N hp hw)
  have hpg := Nat.mul_le_mul hpre hg
  have hn : (pre.foldl normStep (p, g, cs)).2.2.length ≤ N + N ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl normStep (p, g, cs)) ≤ _
  rw [esize_prod, esize_prod, hshape.1, hshape.2.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + (esize g + esize (pre.foldl normStep (p, g, cs)).2.2 + 1) + 1 ≤
    30 * N ^ 3 + 30 * N ^ 2 + 30 * N + 30
  nlinarith [Nat.zero_le (N ^ 3)]

/-- One globally polynomial-time program for a supplied list of polynomial translates. -/
def normProductBitsProg : PolyTimeFun (BitStr × BitStr × List BitStr) (List BitStr) :=
  (snd.comp snd).comp ((foldl normStepProg (30 * X ^ 3 + 30 * X ^ 2 + 30 * X + 30)
    normStep_bounded).comp ((snd.comp snd).pair
      (fst.pair ((fst.comp snd).pair (cons (oneBitsProg.comp fst) (const []))))))

@[simp] theorem normProductBitsProg_apply (p g : BitStr) (as : List BitStr) :
    normProductBitsProg (p, g, as) = normProductBits p g as := rfl

/-- A fixed-width encoding of the canonical quotient root, also valid in degree one. -/
def rootBits (p : BitStr) : BitStr := shiftReduce p (oneBits p)

@[simp] theorem length_rootBits (p : BitStr) : (rootBits p).length = p.length :=
  length_shiftReduce _ _ (length_oneBits p)

def rootBitsProg : PolyTimeFun BitStr BitStr := shiftReduceProg.comp ((PolyTimeFun.id _).pair oneBitsProg)

@[simp] theorem rootBitsProg_apply (p : BitStr) : rootBitsProg p = rootBits p := rfl

/-- Binary output of the composed-sum construction for the supplied monic modulus and polynomial. -/
def composedSumBits (p g : BitStr) : BitStr :=
  descendBits (normProductBits p g (orbitBits (unary p.length) p (rootBits p)))

/-- The composed-sum constructor is polynomial-time on every pair of raw lists. -/
def composedSumBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  let roots := orbitBitsProg.comp ((length.comp fst).pair (fst.pair (rootBitsProg.comp fst)))
  descendBitsProg.comp (normProductBitsProg.comp (fst.pair (snd.pair roots)))

@[simp] theorem composedSumBitsProg_apply (p g : BitStr) :
    composedSumBitsProg (p, g) = composedSumBits p g := rfl

end MIPRE.LowDegree.BinaryQuotient

end


