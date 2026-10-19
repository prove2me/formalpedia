-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
-- name    : MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:14:10.724426+00:00
-- url     : https://prove2.me/theorems/e1f5b848-9a21-4b1b-aedc-20627e70522a
-- title:
--   Definitions of BinaryArtinSchreierLoop: The bounded power-of-two constructor The input is the requested degree in unary
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The bounded power-of-two constructor. The input is the requested degree in unary. The loop caps all intermediate moduli by this input degree, including on malformed states. The unbounded mathematical stage sequence below is used only to state the induction proof.
--
--   **Definitions** (8): `MIPRE.LowDegree.BinaryArtinSchreier.TowerState` (Target degree in unary and the current lower coefficients.); `MIPRE.LowDegree.BinaryArtinSchreier.cappedStep` (Grow only below the target, and cap every replacement by the target width.); `MIPRE.LowDegree.BinaryArtinSchreier.cappedStepProg` (One uniform capped step, including its unary stopping test.); `MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits` (Return the degree-one polynomial for unary zero or one, otherwise run the capped tower.); `MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBitsProg` (A fixed ambient polynomial-time program on the requested degree, not its logarithm.); `MIPRE.LowDegree.BinaryArtinSchreier.stage` (The mathematical sequence used to prove the bounded loop correct.); `MIPRE.LowDegree.BinaryArtinSchreier.towerLoopProg` (Run a polynomially bounded number of capped tower steps.); `_private.MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop.0.MIPRE.LowDegree.BinaryArtinSchreier.isEmptyUnaryProg`.
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cappedStepProg_apply`, `powerTwoBitsProg_apply`, `stage_invariant`, `towerLoopProg_apply`, `cappedStep_bounded`, `cappedStep_stage`, `cappedStep_stage_fixed`, `cappedStep_width`, `fold_cappedStep`, `fold_cappedStep_width`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop` (`MIPRE/Foundations/LowDegree/BinaryArtinSchreierLoop.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 40 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreierLoop.lean; blueprint lem:binary-power-two-irreducible

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierLoop.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
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
import Mathlib.RingTheory.Polynomial.Content
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_initial_invariant
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_towerStep_invariant

/-!
# The bounded power-of-two constructor

The input is the requested degree in unary. The loop caps all intermediate
moduli by this input degree, including on malformed states. The unbounded
mathematical stage sequence below is used only to state the induction proof.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryArtinSchreier

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- The mathematical sequence used to prove the bounded loop correct. -/
def stage : ℕ → BitStr
  | 0 => [true, true]
  | t + 1 => (towerStepBits (stage t)).dropLast

theorem stage_invariant (t : ℕ) : TowerInvariant (stage t) t := by
  induction t with
  | zero => exact initial_invariant
  | succ t ih => exact towerStep_invariant _ _ ih

/-- Target degree in unary and the current lower coefficients. -/
abbrev TowerState := Unary × BitStr

/-- Grow only below the target, and cap every replacement by the target width. -/
def cappedStep (s : TowerState) : TowerState :=
  if (s.1.drop s.2.length).isEmpty then s
  else (s.1, (towerStepBits s.2).dropLast.take s.1.length)

def isEmptyUnaryProg : PolyTimeFun Unary Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.isEmpty (by intro a; cases a <;> rfl)

/-- One uniform capped step, including its unary stopping test. -/
def cappedStepProg : PolyTimeFun TowerState TowerState :=
  congr (ite (isEmptyUnaryProg.comp (drop.comp (fst.pair (length.comp snd)))) (PolyTimeFun.id _)
    (fst.pair (take.comp ((dropLastBitsProg.comp (towerStepBitsProg.comp snd)).pair fst))))
    cappedStep (by
      intro s
      change (if (s.1.drop (unary s.2.length).length).isEmpty then s else
        (s.1, (towerStepBits s.2).dropLast.take s.1.length)) = _
      rw [length_unary]
      rfl)

@[simp] theorem cappedStepProg_apply (s : TowerState) : cappedStepProg s = cappedStep s := rfl

theorem cappedStep_width (s : TowerState) :
    (cappedStep s).1 = s.1 ∧ (cappedStep s).2.length ≤ max s.2.length s.1.length := by
  unfold cappedStep
  split
  · exact ⟨rfl, le_max_left _ _⟩
  · exact ⟨rfl, (List.length_take_le _ _).trans (le_max_right _ _)⟩

theorem fold_cappedStep_width (u : Unary) (s : TowerState) :
    (u.foldl (fun s _ => cappedStep s) s).1 = s.1 ∧
      (u.foldl (fun s _ => cappedStep s) s).2.length ≤ max s.2.length s.1.length := by
  induction u generalizing s with
  | nil => exact ⟨rfl, le_max_left _ _⟩
  | cons x u ih =>
    obtain ⟨hc, hw⟩ := cappedStep_width s
    obtain ⟨hci, hwi⟩ := ih (cappedStep s)
    refine ⟨hci.trans hc, ?_⟩
    rw [hc] at hwi
    exact hwi.trans (max_le hw (le_max_right _ _))

theorem cappedStep_bounded : FoldBounded (cappedStepProg.comp (fst : PolyTimeFun (TowerState × Unit) TowerState)) (6 * X + 6) := by
  intro u s pre post _
  change esize (pre.foldl (fun s _ => cappedStep s) s) ≤ _
  obtain ⟨hc, hw⟩ := fold_cappedStep_width pre s
  have he := esize_bitStr_le (pre.foldl (fun s _ => cappedStep s) s).2
  have hp := length_le_esize_bitStr s.2
  have hu := length_le_esize_list s.1
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hc]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- Run a polynomially bounded number of capped tower steps. -/
def towerLoopProg : PolyTimeFun (Unary × TowerState) TowerState :=
  foldl (cappedStepProg.comp fst) (6 * X + 6) cappedStep_bounded

@[simp] theorem towerLoopProg_apply (u : Unary) (s : TowerState) :
    towerLoopProg (u, s) = u.foldl (fun s _ => cappedStep s) s := rfl

theorem fold_cappedStep (u : Unary) (s : TowerState) :
    u.foldl (fun s _ => cappedStep s) s = cappedStep^[u.length] s := by
  induction u generalizing s with
  | nil => rfl
  | cons x u ih =>
    rw [List.foldl_cons, ih, List.length_cons, Function.iterate_succ_apply]

/-- Return the degree-one polynomial for unary zero or one, otherwise run the capped tower. -/
def powerTwoBits (u : Unary) : BitStr :=
  if u.tail.isEmpty then [false, true]
  else (u.foldl (fun s _ => cappedStep s) (u, [true, true])).2 ++ [true]

/-- A fixed ambient polynomial-time program on the requested degree, not its logarithm. -/
def powerTwoBitsProg : PolyTimeFun Unary BitStr :=
  ite (isEmptyUnaryProg.comp tail) (const [false, true])
    (append.comp ((snd.comp (towerLoopProg.comp
      ((PolyTimeFun.id _).pair ((PolyTimeFun.id _).pair (const [true, true]))))).pair (const [true])))

@[simp] theorem powerTwoBitsProg_apply (u : Unary) : powerTwoBitsProg u = powerTwoBits u := rfl

theorem cappedStep_stage (u : Unary) (t : ℕ) (h : 2 ^ (t + 1 + 1) ≤ u.length) :
    cappedStep (u, stage t) = (u, stage (t + 1)) := by
  have hw := (stage_invariant t).width
  have hn := Nat.two_pow_pos (t + 1)
  have hg : (stage t).length < u.length := by
    rw [pow_succ] at h
    omega
  have hb : (u.drop (stage t).length).isEmpty = false := by
    cases he : u.drop (stage t).length with
    | nil =>
      have hh := congrArg List.length he
      simp only [List.length_drop, List.length_nil] at hh
      omega
    | cons x xs => rfl
  simp only [cappedStep, hb, Bool.false_eq_true, ↓reduceIte]
  change (u, (stage (t + 1)).take u.length) = (u, stage (t + 1))
  rw [List.take_of_length_le (by rw [(stage_invariant (t + 1)).width]; exact h)]

theorem iterate_cappedStep_stage (u : Unary) (t : ℕ)
    (h : 2 ^ (t + 1) ≤ u.length) :
    cappedStep^[t] (u, [true, true]) = (u, stage t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp : 2 ^ (t + 1) ≤ u.length := by
      rw [pow_succ] at h
      omega
    rw [Function.iterate_succ_apply', ih hp]
    exact cappedStep_stage u t h

theorem cappedStep_stage_fixed (u : Unary) (t : ℕ) (h : u.length = 2 ^ (t + 1)) :
    cappedStep (u, stage t) = (u, stage t) := by
  simp [cappedStep, (stage_invariant t).width, ← h]

theorem iterate_cappedStep_finished (u : Unary) (t : ℕ) (h : u.length = 2 ^ (t + 1)) :
    cappedStep^[u.length] (u, [true, true]) = (u, stage t) := by
  have ht : t ≤ u.length := by
    rw [h]
    have hn := (t + 1).lt_two_pow_self
    omega
  have hinit := iterate_cappedStep_stage u t h.ge
  have hfixed := cappedStep_stage_fixed u t h
  have hrepeat (k : ℕ) : cappedStep^[k] (u, stage t) = (u, stage t) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hfixed, ih]
  rw [show u.length = (u.length - t) + t by omega, Function.iterate_add_apply, hinit]
  exact hrepeat _

end MIPRE.LowDegree.BinaryArtinSchreier

end


