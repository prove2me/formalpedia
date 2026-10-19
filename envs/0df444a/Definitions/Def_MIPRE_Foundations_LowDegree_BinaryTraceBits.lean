-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
-- name    : MIPRE_Foundations_LowDegree_BinaryTraceBits
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:59.200985+00:00
-- url     : https://prove2.me/theorems/854ffd58-3231-40a7-b531-31b046c03580
-- title:
--   Definitions of BinaryTraceBits: Explicit polynomial-time Frobenius-stride traces
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryTraceBits` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Explicit polynomial-time Frobenius-stride traces
--
--   **Definitions** (9): `MIPRE.LowDegree.BinaryQuotient.TraceState` (Stride, modulus, accumulated sum, and the current Frobenius conjugate.); `MIPRE.LowDegree.BinaryQuotient.frobeniusBits` (A supplied unary number of squarings in the explicit binary quotient.); `MIPRE.LowDegree.BinaryQuotient.frobeniusBitsProg` (The stride Frobenius program is globally polynomially bounded.); `MIPRE.LowDegree.BinaryQuotient.squareFuel` (Repeat squaring once per unary stride bit.); `MIPRE.LowDegree.BinaryQuotient.traceBits` (The binary vector for the sum of the requested Frobenius-stride conjugates.); `MIPRE.LowDegree.BinaryQuotient.traceBitsProg` (One globally polynomial-time program computes every such modular trace sum.); `MIPRE.LowDegree.BinaryQuotient.traceStep` (Add the current conjugate and advance by the fixed Frobenius stride.); `_private.MIPRE.Foundations.LowDegree.BinaryTraceBits.0.MIPRE.LowDegree.BinaryQuotient.squareFuelProg`; `_private.MIPRE.Foundations.LowDegree.BinaryTraceBits.0.MIPRE.LowDegree.BinaryQuotient.traceStepProg`.
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fold_squareFuel`, `fold_traceStep_shape`, `frobeniusBitsProg_apply`, `frobeniusBits_width_le`, `traceBitsProg_apply`, `squareFuel_bounded`, `traceStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryTraceBits` (`MIPRE/Foundations/LowDegree/BinaryTraceBits.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryTraceBits.lean; blueprint lem:binary-odd-prime-power-irreducible

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryTraceBits.lean (definition bundle: declarations the uploaded statements rest on);
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

/-! # Explicit polynomial-time Frobenius-stride traces -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Repeat squaring once per unary stride bit. -/
def squareFuel (s : SquareState) (_ : Unit) : SquareState := squareStep s

theorem fold_squareFuel (u : Unary) (s : SquareState) :
    u.foldl squareFuel s = squareStep^[u.length] s := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih => simpa only [List.foldl_cons, List.length_cons,
      Function.iterate_succ_apply, squareFuel] using ih (squareStep s)

def squareFuelProg : PolyTimeFun (SquareState × Unit) SquareState :=
  (fst.comp fst).pair (squareProg.comp fst)

theorem squareFuel_bounded : FoldBounded squareFuelProg (5 * X + 5) := by
  intro l s pre post _
  change esize (pre.foldl squareFuel s) ≤ _
  rw [fold_squareFuel]
  obtain ⟨hm, hw⟩ := iterate_squareStep_shape pre.length s
  have ha := esize_bitStr_le (squareStep^[pre.length] s).2
  have hb := length_le_esize_bitStr s.2
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hm]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- A supplied unary number of squarings in the explicit binary quotient. -/
def frobeniusBits (u : Unary) (p a : BitStr) : BitStr :=
  (squareStep^[u.length] (p, a)).2

/-- The stride Frobenius program is globally polynomially bounded. -/
def frobeniusBitsProg : PolyTimeFun (Unary × BitStr × BitStr) BitStr :=
  snd.comp (foldl squareFuelProg (5 * X + 5) squareFuel_bounded)

@[simp] theorem frobeniusBitsProg_apply (u : Unary) (p a : BitStr) :
    frobeniusBitsProg (u, p, a) = frobeniusBits u p a := by
  change (u.foldl squareFuel (p, a)).2 = _
  rw [fold_squareFuel]
  rfl

/-- Repeated squaring never increases even a malformed coefficient width. -/
theorem frobeniusBits_width_le (u : Unary) (p a : BitStr) :
    (frobeniusBits u p a).length ≤ a.length := (iterate_squareStep_shape u.length (p, a)).2

/-- Stride, modulus, accumulated sum, and the current Frobenius conjugate. -/
abbrev TraceState := Unary × BitStr × BitStr × BitStr

/-- Add the current conjugate and advance by the fixed Frobenius stride. -/
def traceStep (s : TraceState) (_ : Unit) : TraceState :=
  (s.1, s.2.1, xorBits s.2.2.1 s.2.2.2, frobeniusBits s.1 s.2.1 s.2.2.2)

/-- All runtime state widths stay below their initial widths. -/
theorem fold_traceStep_shape (u : Unary) (s : TraceState) :
    (u.foldl traceStep s).1 = s.1 ∧ (u.foldl traceStep s).2.1 = s.2.1 ∧
    (u.foldl traceStep s).2.2.1.length ≤ s.2.2.1.length ∧
    (u.foldl traceStep s).2.2.2.length ≤ s.2.2.2.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, rfl, le_rfl, le_rfl⟩
  | cons b u ih =>
    obtain ⟨hr, hp, hc, ha⟩ := ih (traceStep s b)
    refine ⟨hr, hp, hc.trans ?_, ha.trans (frobeniusBits_width_le ..)⟩
    simp only [traceStep, xorBits, List.length_zipWith]
    exact min_le_left _ _

def traceStepProg : PolyTimeFun (TraceState × Unit) TraceState :=
  let r := fst.comp fst
  let p := fst.comp (snd.comp fst)
  let c := fst.comp (snd.comp (snd.comp fst))
  let a := snd.comp (snd.comp (snd.comp fst))
  congr (r.pair (p.pair ((xorBitsProg.comp (c.pair a)).pair
    (frobeniusBitsProg.comp (r.pair (p.pair a))))))
    (fun s => traceStep s.1 s.2) (by
      intro s
      simp only [r, p, c, a, comp_apply, pair_apply, fst_apply, snd_apply,
        xorBitsProg_apply, frobeniusBitsProg_apply]
      rfl)

theorem traceStep_bounded : FoldBounded traceStepProg (10 * X + 10) := by
  intro l s pre post _
  change esize (pre.foldl traceStep s) ≤ _
  obtain ⟨hr, hp, hc, ha⟩ := fold_traceStep_shape pre s
  have hce := esize_bitStr_le (pre.foldl traceStep s).2.2.1
  have hae := esize_bitStr_le (pre.foldl traceStep s).2.2.2
  have hc0 := length_le_esize_bitStr s.2.2.1
  have ha0 := length_le_esize_bitStr s.2.2.2
  have hs : esize s = esize s.1 + (esize s.2.1 +
    (esize s.2.2.1 + esize s.2.2.2 + 1) + 1) + 1 := rfl
  change esize (pre.foldl traceStep s).1 + (esize (pre.foldl traceStep s).2.1 +
    (esize (pre.foldl traceStep s).2.2.1 + esize (pre.foldl traceStep s).2.2.2 + 1) + 1) + 1 ≤ _
  rw [hr, hp]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- The binary vector for the sum of the requested Frobenius-stride conjugates. -/
def traceBits (m r : Unary) (p a : BitStr) : BitStr :=
  (m.foldl traceStep (r, p, zeroBits p, a)).2.2.1

/-- One globally polynomial-time program computes every such modular trace sum. -/
def traceBitsProg : PolyTimeFun (Unary × Unary × BitStr × BitStr) BitStr :=
  let m := fst
  let r := fst.comp snd
  let p := fst.comp (snd.comp snd)
  let a := snd.comp (snd.comp snd)
  (fst.comp (snd.comp snd)).comp
    ((foldl traceStepProg (10 * X + 10) traceStep_bounded).comp
      (m.pair (r.pair (p.pair ((zeroBitsProg.comp p).pair a)))))

@[simp] theorem traceBitsProg_apply (m r : Unary) (p a : BitStr) :
    traceBitsProg (m, r, p, a) = traceBits m r p a := by
  simp only [traceBitsProg, comp_apply, pair_apply, fst_apply, snd_apply, zeroBitsProg_apply]
  rfl

end MIPRE.LowDegree.BinaryQuotient

end


