-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
-- name    : MIPRE_Foundations_LowDegree_BinaryQuotientComponents
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:39.138475+00:00
-- url     : https://prove2.me/theorems/c658389f-e52d-4dfe-8f82-2822e61983f8
-- title:
--   Definitions of BinaryQuotientComponents: Bounded component separation in binary polynomial quotients Refine the unit by a supplied family of Frobenius-fixed…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryQuotientComponents` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bounded component separation in binary polynomial quotients. Refine the unit by a supplied family of Frobenius-fixed vectors. The component count is clipped to the quotient dimension on every iteration; the algebraic orthogonality invariant proves that clipping is inert on valid inputs.
--
--   **Definitions** (12): `MIPRE.LowDegree.BinaryQuotient.ComponentState` (Quotient modulus together with its current component list.); `MIPRE.LowDegree.BinaryQuotient.componentStep` (Refine once by the next supplied fixed-space generator.); `MIPRE.LowDegree.BinaryQuotient.components` (The abstract component family produced by separating all fixed-space generators.); `MIPRE.LowDegree.BinaryQuotient.componentsBits` (Refine the unit by the supplied fixed-space generator list.); `MIPRE.LowDegree.BinaryQuotient.componentsBitsProg` (Uniform polynomial-time quotient component separation.); `MIPRE.LowDegree.BinaryQuotient.fixedFamily` (The Frobenius-fixed family in the program's specified deterministic order.); `MIPRE.LowDegree.BinaryQuotient.quotientComponentsProg` (Compute the primitive component encodings from the monic modulus alone.); `MIPRE.LowDegree.BinaryQuotient.splitBits` (One quotient split uses modular multiplication, XOR, and a zero test.); `MIPRE.LowDegree.BinaryQuotient.splitBitsCapped` (Refine the component list and retain at most the quotient dimension.); `MIPRE.LowDegree.BinaryQuotient.splitBitsCappedProg` (Refine a raw list with one generator and apply the dimension cap.); `MIPRE.LowDegree.BinaryQuotient.splitBitsProg` (A single raw component split as a polynomial-time ambient program.); `_private.MIPRE.Foundations.LowDegree.BinaryQuotientComponents.0.MIPRE.LowDegree.BinaryQuotient.componentStepProg`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `componentsBitsProg_apply`, `fold_componentStep_length`, `fold_componentStep_modulus`, `fold_componentStep_width`, `splitBitsCappedProg_apply`, `splitBitsCapped_width`, `splitBits_width`, `componentStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryQuotientComponents` (`MIPRE/Foundations/LowDegree/BinaryQuotientComponents.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientComponents.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientComponents.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_esize_rows_of_width
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-!
# Bounded component separation in binary polynomial quotients

Refine the unit by a supplied family of Frobenius-fixed vectors. The component
count is clipped to the quotient dimension on every iteration; the algebraic
orthogonality invariant proves that clipping is inert on valid inputs.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- One quotient split uses modular multiplication, XOR, and a zero test. -/
def splitBits (p e b : BitStr) : List BitStr :=
  let x := mulReduce p e b
  [x, xorBits e x].filter BinaryLinear.nonzeroRow

/-- Splitting never increases any component's coefficient width. -/
theorem splitBits_width (p e b : BitStr) : ∀ x ∈ splitBits p e b, x.length ≤ e.length := by
  intro x hx
  have hm := (List.mem_filter.mp hx).1
  rcases List.mem_cons.mp hm with rfl | hm
  · exact length_mulReduce_le _ _ _
  · rw [List.mem_singleton.mp hm, length_xorBits]
    exact min_le_left _ _

/-- Refine the component list and retain at most the quotient dimension. -/
def splitBitsCapped (p : BitStr) (l : List BitStr) (b : BitStr) : List BitStr :=
  (l.flatMap (fun e => splitBits p e b)).take p.length

/-- Quotient modulus together with its current component list. -/
abbrev ComponentState := BitStr × List BitStr

/-- Refine once by the next supplied fixed-space generator. -/
def componentStep (s : ComponentState) (b : BitStr) : ComponentState :=
  (s.1, splitBitsCapped s.1 s.2 b)

/-- Refinement retains the modulus. -/
theorem fold_componentStep_modulus (bs : List BitStr) (p : BitStr) (l : List BitStr) :
    (bs.foldl componentStep (p, l)).1 = p := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Refined lists retain the original coefficient-width bound. -/
theorem splitBitsCapped_width (p : BitStr) (l : List BitStr) (b : BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) : ∀ e ∈ splitBitsCapped p l b, e.length ≤ N := by
  intro e he
  obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp (List.mem_of_mem_take he)
  exact (splitBits_width p x b e he).trans (hl x hx)

/-- Every partial refinement has the original maximum component width. -/
theorem fold_componentStep_width (bs : List BitStr) (p : BitStr) (l : List BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) :
    ∀ e ∈ (bs.foldl componentStep (p, l)).2, e.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih => exact ih _ (splitBitsCapped_width p l b N hl)

/-- The cap bounds the number of components even for malformed inputs. -/
theorem fold_componentStep_length (bs : List BitStr) (p : BitStr) (l : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hl : l.length ≤ N) :
    (bs.foldl componentStep (p, l)).2.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih => exact ih _ ((List.length_take_le _ _).trans hp)

/-- A single raw component split as a polynomial-time ambient program. -/
def splitBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) (List BitStr) :=
  let e := fst.comp snd
  congr (append.comp ((BinaryLinear.keepRowProg.comp mulReduceProg).pair
    (BinaryLinear.keepRowProg.comp (xorBitsProg.comp (e.pair mulReduceProg)))))
    (fun s => splitBits s.1 s.2.1 s.2.2) (by
      intro s
      change (if BinaryLinear.nonzeroRow (mulReduce s.1 s.2.1 s.2.2)
        then [mulReduce s.1 s.2.1 s.2.2] else []) ++
        (if BinaryLinear.nonzeroRow (xorBits s.2.1 (mulReduce s.1 s.2.1 s.2.2))
        then [xorBits s.2.1 (mulReduce s.1 s.2.1 s.2.2)] else []) = _
      unfold splitBits
      split <;> split <;> simp_all)

/-- Refine a raw list with one generator and apply the dimension cap. -/
def splitBitsCappedProg : PolyTimeFun (BitStr × List BitStr × BitStr) (List BitStr) :=
  let split : PolyTimeFun (BitStr × (BitStr × BitStr)) (List BitStr) :=
    splitBitsProg.comp ((fst.comp snd).pair (fst.pair (snd.comp snd)))
  congr (take.comp ((BinaryLinear.flattenBitsProg.comp ((mapWith split).comp
    ((fst.comp snd).pair (fst.pair (snd.comp snd))))).pair (length.comp fst)))
    (fun s => splitBitsCapped s.1 s.2.1 s.2.2) (by
      intro s
      change (List.flatten (s.2.1.map (fun e => splitBits s.1 e s.2.2))).take
        (unary s.1.length).length = _
      simp only [length_unary, splitBitsCapped, List.flatMap_def])

@[simp] theorem splitBitsCappedProg_apply (p : BitStr) (l : List BitStr) (b : BitStr) :
    splitBitsCappedProg (p, l, b) = splitBitsCapped p l b := rfl

def componentStepProg : PolyTimeFun (ComponentState × BitStr) ComponentState :=
  (fst.comp fst).pair (splitBitsCappedProg.comp
    ((fst.comp fst).pair ((snd.comp fst).pair snd)))

theorem componentStep_bounded : FoldBounded componentStepProg (5 * X ^ 2 + 5 * X + 5) := by
  intro bs s pre post _
  rcases s with ⟨p, l⟩
  let N := esize (bs, p, l)
  have hp : p.length ≤ N := by
    have h := length_le_esize_list p
    simp only [N, esize_prod]
    omega
  have hl : l.length ≤ N := by
    have h := length_le_esize_list l
    simp only [N, esize_prod]
    omega
  have hw : ∀ e ∈ l, e.length ≤ N := by
    intro e he
    have h₁ := esize_mem_le he
    have h₂ := length_le_esize_bitStr e
    simp only [N, esize_prod]
    omega
  have hh := BinaryLinear.esize_rows_of_width _ N (fold_componentStep_width pre p l N hw)
  have hn := fold_componentStep_length pre p l N hp hl
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl componentStep (p, l)) ≤ _
  rw [esize_prod, fold_componentStep_modulus]
  have he : esize p ≤ N := by simp only [N, esize_prod]; omega
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + esize (pre.foldl componentStep (p, l)).2 + 1 ≤ 5 * N ^ 2 + 5 * N + 5
  nlinarith

/-- Refine the unit by the supplied fixed-space generator list. -/
def componentsBits (p : BitStr) (bs : List BitStr) : List BitStr :=
  (bs.foldl componentStep (p, [oneBits p])).2

/-- Uniform polynomial-time quotient component separation. -/
def componentsBitsProg : PolyTimeFun (BitStr × List BitStr) (List BitStr) :=
  snd.comp ((foldl componentStepProg (5 * X ^ 2 + 5 * X + 5) componentStep_bounded).comp
    (snd.pair (fst.pair (cons (oneBitsProg.comp fst) (const [])))))

@[simp] theorem componentsBitsProg_apply (p : BitStr) (bs : List BitStr) :
    componentsBitsProg (p, bs) = componentsBits p bs := rfl

/-- The Frobenius-fixed family in the program's specified deterministic order. -/
def fixedFamily : List (AdjoinRoot f) := List.ofFn (fixedGenerator f hf)

/-- The abstract component family produced by separating all fixed-space generators. -/
def components : List (AdjoinRoot f) := splitAllComponents [1] (fixedFamily f hf)

/-- Compute the primitive component encodings from the monic modulus alone. -/
def quotientComponentsProg : PolyTimeFun BitStr (List BitStr) :=
  componentsBitsProg.comp ((PolyTimeFun.id _).pair fixedGeneratorsProg)

end MIPRE.LowDegree.BinaryQuotient

end


