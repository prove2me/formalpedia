-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
-- name    : MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:51:38.170986+00:00
-- url     : https://prove2.me/theorems/ca540ecb-9c07-4c3d-8673-fc6e57ea3c77
-- title:
--   Definitions of BinaryNonresidueLoop: Bounded auxiliary root lifting This is the specified program for the odd-prime auxiliary stage
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryNonresidueLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bounded auxiliary root lifting. This is the specified program for the odd-prime auxiliary stage. It repeatedly factors `f(X^q)`, retaining the current `f` once factorization returns at most one factor. Nonterminal choices are clipped to the initial seed width, ensuring a global runtime bound even on malformed inputs. The statements here establish execution and size bounds; the nonresidue and termination correctness theorems are separate algebraic obligations.
--
--   **Definitions** (9): `MIPRE.LowDegree.BinaryPolynomial.NonresidueState` (Exponent minus one in unary, coefficient cap, done flag, and current polynomial.); `MIPRE.LowDegree.BinaryPolynomial.liftCandidates` (Factor the positive-power substitution in the current candidate.); `MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg` (The retained binary polynomial from the bounded auxiliary construction.); `MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftStateProg` (The auxiliary root-lifting program initialized from the deterministic cyclotomic seed.); `MIPRE.LowDegree.BinaryPolynomial.nonresidueLoopProg` (Run the bounded lifting loop with explicitly supplied fuel and metadata.); `MIPRE.LowDegree.BinaryPolynomial.nonresidueStep` (One bounded root-lifting step, retaining the old polynomial at the stopping test.); `_private.MIPRE.Foundations.LowDegree.BinaryNonresidueLoop.0.MIPRE.LowDegree.BinaryPolynomial.isEmptyProg`; `_private.MIPRE.Foundations.LowDegree.BinaryNonresidueLoop.0.MIPRE.LowDegree.BinaryPolynomial.liftCandidatesProg`; `_private.MIPRE.Foundations.LowDegree.BinaryNonresidueLoop.0.MIPRE.LowDegree.BinaryPolynomial.nonresidueStepProg`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fold_nonresidueStep_width`, `nonresidueLoopProg_apply`, `nonresidueStep_width`, `nonresidueStep_bounded`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryNonresidueLoop` (`MIPRE/Foundations/LowDegree/BinaryNonresidueLoop.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 45 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryNonresidueLoop.lean; blueprint lem:binary-odd-prime-nonresidue

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryNonresidueLoop.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution

/-!
# Bounded auxiliary root lifting

This is the specified program for the odd-prime auxiliary stage. It repeatedly
factors `f(X^q)`, retaining the current `f` once factorization returns at most one
factor. Nonterminal choices are clipped to the initial seed width, ensuring a
global runtime bound even on malformed inputs. The statements here establish
execution and size bounds; the nonresidue and termination correctness theorems
are separate algebraic obligations.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Exponent minus one in unary, coefficient cap, done flag, and current polynomial. -/
abbrev NonresidueState := Unary × Unary × Bool × BitStr

/-- Factor the positive-power substitution in the current candidate. -/
noncomputable def liftCandidates (s : NonresidueState) : List BitStr :=
  BinaryQuotient.factorBitsProg ((substitutePowerBits s.2.2.2 s.1).dropLast)

/-- One bounded root-lifting step, retaining the old polynomial at the stopping test. -/
noncomputable def nonresidueStep (s : NonresidueState) (_ : Bool) : NonresidueState :=
  if s.2.2.1 then s else
    if (liftCandidates s).tail.isEmpty then (s.1, s.2.1, true, s.2.2.2)
    else (s.1, s.2.1, false, ((liftCandidates s).headD []).take s.2.1.length)

/-- Each step retains both external parameters and respects the original width cap. -/
theorem nonresidueStep_width (s : NonresidueState) (b : Bool) :
    (nonresidueStep s b).1 = s.1 ∧ (nonresidueStep s b).2.1 = s.2.1 ∧
    (nonresidueStep s b).2.2.2.length ≤ max s.2.2.2.length s.2.1.length := by
  unfold nonresidueStep
  split
  · exact ⟨rfl, rfl, le_max_left _ _⟩
  · split
    · exact ⟨rfl, rfl, le_max_left _ _⟩
    · exact ⟨rfl, rfl, (List.length_take_le _ _).trans (le_max_right _ _)⟩

/-- The complete loop retains metadata and never exceeds the initial maximum width. -/
theorem fold_nonresidueStep_width (l : BitStr) (s : NonresidueState) :
    (l.foldl nonresidueStep s).1 = s.1 ∧ (l.foldl nonresidueStep s).2.1 = s.2.1 ∧
    (l.foldl nonresidueStep s).2.2.2.length ≤ max s.2.2.2.length s.2.1.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, le_max_left _ _⟩
  | cons b l ih =>
    obtain ⟨hq, hc, hf⟩ := nonresidueStep_width s b
    obtain ⟨hqi, hci, hfi⟩ := ih (nonresidueStep s b)
    refine ⟨hqi.trans hq, hci.trans hc, ?_⟩
    rw [hc] at hfi
    exact hfi.trans (max_le hf (le_max_right _ _))

noncomputable def isEmptyProg_BinaryNonresidueLoop : PolyTimeFun (List BitStr) Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

noncomputable def liftCandidatesProg : PolyTimeFun NonresidueState (List BitStr) :=
  congr (BinaryQuotient.factorBitsProg.comp (dropLastBitsProg.comp
    (substitutePowerBitsProg.comp ((snd.comp (snd.comp snd)).pair fst))))
    liftCandidates (by intro s; rfl)

set_option maxHeartbeats 2000000 in
noncomputable def nonresidueStepProg : PolyTimeFun (NonresidueState × Bool) NonresidueState :=
  let q := fst.comp fst
  let cap := fst.comp (snd.comp fst)
  let done := fst.comp (snd.comp (snd.comp fst))
  let f := snd.comp (snd.comp (snd.comp fst))
  let candidates := liftCandidatesProg.comp fst
  congr (ite done fst (ite (isEmptyProg_BinaryNonresidueLoop.comp (PolyTimeFun.tail.comp candidates))
    (q.pair (cap.pair ((const true).pair f)))
    (q.pair (cap.pair ((const false).pair
      (take.comp (((PolyTimeFun.headD []).comp candidates).pair cap)))))))
    (fun s => nonresidueStep s.1 s.2) (by intro s; rfl)

theorem nonresidueStep_bounded : FoldBounded nonresidueStepProg (10 * X + 10) := by
  intro l s pre post _
  change esize (pre.foldl nonresidueStep s) ≤ _
  obtain ⟨hq, hc, hf⟩ := fold_nonresidueStep_width pre s
  have hsz := esize_bitStr_le (pre.foldl nonresidueStep s).2.2.2
  have hinit := length_le_esize_list s.2.2.2
  have hcap := length_le_esize_list s.2.1
  have hflag : esize (pre.foldl nonresidueStep s).2.2.1 ≤ 3 := by
    cases (pre.foldl nonresidueStep s).2.2.1 <;> decide
  have hs : esize s = esize s.1 + (esize s.2.1 +
    (esize s.2.2.1 + esize s.2.2.2 + 1) + 1) + 1 := rfl
  change esize (pre.foldl nonresidueStep s).1 + (esize (pre.foldl nonresidueStep s).2.1 +
    (esize (pre.foldl nonresidueStep s).2.2.1 + esize (pre.foldl nonresidueStep s).2.2.2 + 1) + 1) + 1 ≤ _
  rw [hq, hc]
  simp only [esize_prod, hs, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- Run the bounded lifting loop with explicitly supplied fuel and metadata. -/
noncomputable def nonresidueLoopProg : PolyTimeFun (BitStr × NonresidueState) NonresidueState :=
  foldl nonresidueStepProg (10 * X + 10) nonresidueStep_bounded

@[simp] theorem nonresidueLoopProg_apply (l : BitStr) (s : NonresidueState) :
    nonresidueLoopProg (l, s) = l.foldl nonresidueStep s := rfl

/-- The auxiliary root-lifting program initialized from the deterministic cyclotomic seed.
The initial seed degree supplies the iteration budget, and its full width supplies the cap. -/
noncomputable def nonresidueLiftStateProg : PolyTimeFun Unary NonresidueState :=
  let seed := cyclotomicSeedBitsProg
  nonresidueLoopProg.comp ((PolyTimeFun.tail.comp seed).pair
    (PolyTimeFun.tail.pair ((length.comp seed).pair ((const false).pair seed))))

/-- The retained binary polynomial from the bounded auxiliary construction. -/
noncomputable def nonresidueLiftBitsProg : PolyTimeFun Unary BitStr :=
  (snd.comp (snd.comp snd)).comp nonresidueLiftStateProg

end MIPRE.LowDegree.BinaryPolynomial


