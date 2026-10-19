-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
-- name    : MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:15.36867+00:00
-- url     : https://prove2.me/theorems/4703c2ad-143e-49e4-b2a5-9941ea86bc80
-- title:
--   Definitions of BinaryQuotientPolynomial: Polynomial arithmetic with supplied binary-quotient coefficient vectors
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial arithmetic with supplied binary-quotient coefficient vectors
--
--   **Definitions** (11): `MIPRE.LowDegree.BinaryQuotient.addCoeffLists` (Add coefficient lists, keeping unmatched final coefficients.); `MIPRE.LowDegree.BinaryQuotient.addCoeffListsProg` (One globally polynomial-time coefficient addition program.); `MIPRE.LowDegree.BinaryQuotient.mulCoeffLists` (Horner multiplication of two polynomial coefficient lists.); `MIPRE.LowDegree.BinaryQuotient.mulCoeffListsProg` (A globally polynomial-time product of two supplied-quotient coefficient lists.); `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.AddState`; `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.MulState`; `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.addStep`; `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.addStepProg`; `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.finishAdd`; `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.mulStep`; `_private.MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial.0.MIPRE.LowDegree.BinaryQuotient.mulStepProg`.
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `addCoeffListsProg_apply`, `addCoeffLists_nil_right`, `addCoeffLists_width_le`, `length_addCoeffLists`, `mulCoeffListsProg_apply`, `addStepProg_apply`, `addStep_growth`, `finishAdd_fold`, `fold_mulStep_eq`, `fold_mulStep_shape`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryQuotientPolynomial` (`MIPRE/Foundations/LowDegree/BinaryQuotientPolynomial.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 34 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientPolynomial.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientPolynomial.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce_le

/-! # Polynomial arithmetic with supplied binary-quotient coefficient vectors -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Add coefficient lists, keeping unmatched final coefficients. -/
def addCoeffLists : List BitStr → List BitStr → List BitStr
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => xorBits a b :: addCoeffLists as bs

@[simp] theorem addCoeffLists_nil_right (as : List BitStr) : addCoeffLists as [] = as := by
  cases as <;> rfl

@[simp] theorem length_addCoeffLists (as bs : List BitStr) :
    (addCoeffLists as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [addCoeffLists]
  | cons a as ih =>
    cases bs <;> simp [addCoeffLists, ih, Nat.succ_max_succ]

/-- Addition cannot exceed a common bound on the input coefficient widths. -/
theorem addCoeffLists_width_le (as bs : List BitStr) (n : ℕ)
    (ha : ∀ a ∈ as, a.length ≤ n) (hb : ∀ b ∈ bs, b.length ≤ n) :
    ∀ c ∈ addCoeffLists as bs, c.length ≤ n := by
  induction as generalizing bs with
  | nil => exact hb
  | cons a as ih =>
    cases bs with
    | nil => exact ha
    | cons b bs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (by rw [length_xorBits]; exact (min_le_left _ _).trans (ha a (by simp)))
      · exact ih bs (fun d hd => ha d (by simp [hd])) (fun d hd => hb d (by simp [hd])) c hc

variable {R : Type*} [CommRing R]

abbrev AddState := List BitStr × List BitStr

def addStep (s : AddState) (a : BitStr) : AddState :=
  match s.1 with
  | [] => ([], a :: s.2)
  | b :: bs => (bs, xorBits a b :: s.2)

def finishAdd (s : AddState) : List BitStr := s.2.reverse ++ s.1

theorem finishAdd_fold (as bs acc : List BitStr) :
    finishAdd (as.foldl addStep (bs, acc)) = acc.reverse ++ addCoeffLists as bs := by
  induction as generalizing bs acc with
  | nil => rfl
  | cons a as ih =>
    cases bs with
    | nil =>
      rw [List.foldl_cons]
      change finishAdd (as.foldl addStep ([], a :: acc)) = _
      rw [ih]
      simp [addCoeffLists, List.append_assoc]
    | cons b bs =>
      rw [List.foldl_cons]
      change finishAdd (as.foldl addStep (bs, xorBits a b :: acc)) = _
      rw [ih]
      simp [addCoeffLists, List.append_assoc]

def addStepProg : PolyTimeFun (AddState × BitStr) AddState :=
  let nilCase : PolyTimeFun (AddState × BitStr) AddState :=
    (const []).pair (cons snd (snd.comp fst))
  let consCase : PolyTimeFun ((AddState × BitStr) × (BitStr × List BitStr)) AddState :=
    (snd.comp snd).pair
      (cons (xorBitsProg.comp ((snd.comp fst).pair (fst.comp snd)))
        (snd.comp (fst.comp fst)))
  (casesList nilCase consCase).comp ((PolyTimeFun.id _).pair (fst.comp fst))

theorem addStepProg_apply (s : AddState) (a : BitStr) :
    addStepProg (s, a) = addStep s a := by
  rcases s with ⟨bs, acc⟩
  cases bs <;> rfl

theorem addStep_growth (s : AddState) (a : BitStr) :
    esize (addStepProg (s, a)) ≤ esize s + (5 * X + 5 : Polynomial ℕ).eval (esize a) := by
  rw [addStepProg_apply]
  rcases s with ⟨bs, acc⟩
  cases bs with
  | nil => simp [addStep, esize_prod, esize_list_cons]; omega
  | cons b bs =>
    have hw : (xorBits a b).length ≤ a.length := by rw [length_xorBits]; exact min_le_left _ _
    have hs := esize_bitStr_le (xorBits a b)
    have ha := length_le_esize_bitStr a
    simp only [addStep, esize_prod, esize_list_cons, eval_add, eval_mul, eval_ofNat, eval_X]
    omega

/-- One globally polynomial-time coefficient addition program. -/
def addCoeffListsProg : PolyTimeFun (List BitStr × List BitStr) (List BitStr) :=
  let scan := foldl addStepProg (X + X * (5 * X + 5))
    (foldBounded_of_additive addStepProg (5 * X + 5) addStep_growth)
  congr (append.comp ((reverse.comp (snd.comp (scan.comp (fst.pair (snd.pair (const [])))))).pair
    (fst.comp (scan.comp (fst.pair (snd.pair (const [])))))))
    (fun q => addCoeffLists q.1 q.2) (by
      rintro ⟨as, bs⟩
      have hstep : addStepProg.step = addStep := by
        funext s a
        exact addStepProg_apply s a
      change finishAdd (as.foldl addStepProg.step (bs, [])) = _
      rw [hstep]
      exact finishAdd_fold as bs [])

@[simp] theorem addCoeffListsProg_apply (as bs : List BitStr) :
    addCoeffListsProg (as, bs) = addCoeffLists as bs := rfl

/-- Horner multiplication of two polynomial coefficient lists. -/
def mulCoeffLists (p : BitStr) : List BitStr → List BitStr → List BitStr
  | [], _ => []
  | a :: as, bs => addCoeffLists (bs.map (mulReduce p a)) (zeroBits p :: mulCoeffLists p as bs)

abbrev MulState := BitStr × List BitStr × List BitStr

def mulStep (s : MulState) (a : BitStr) : MulState :=
  (s.1, s.2.1, addCoeffLists (s.2.1.map (mulReduce s.1 a)) (zeroBits s.1 :: s.2.2))

theorem fold_mulStep_shape (pre : List BitStr) (p : BitStr) (bs cs : List BitStr) :
    (pre.foldl mulStep (p, bs, cs)).1 = p ∧ (pre.foldl mulStep (p, bs, cs)).2.1 = bs ∧
      (pre.foldl mulStep (p, bs, cs)).2.2.length ≤ max bs.length cs.length + pre.length := by
  induction pre generalizing cs with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons a pre ih =>
    have h := ih (addCoeffLists (bs.map (mulReduce p a)) (zeroBits p :: cs))
    refine ⟨h.1, h.2.1, ?_⟩
    simp only [length_addCoeffLists, List.length_map, List.length_cons] at h
    change (pre.foldl mulStep (p, bs, addCoeffLists (bs.map (mulReduce p a))
      (zeroBits p :: cs))).2.2.length ≤ _
    simp only [List.length_cons]
    omega

theorem fold_mulStep_width (pre : List BitStr) (p : BitStr) (bs cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (ha : ∀ a ∈ pre, a.length ≤ N) (hc : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (pre.foldl mulStep (p, bs, cs)).2.2, c.length ≤ N := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons a pre ih =>
    apply ih _ (fun d hd => ha d (by simp [hd]))
    apply addCoeffLists_width_le
    · intro c hc'
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
      exact (length_mulReduce_le p a b).trans (ha a (by simp))
    · intro c hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · simpa using hp
      · exact hc c hc'

theorem fold_mulStep_eq (as : List BitStr) (p : BitStr) (bs cs : List BitStr) :
    as.foldl mulStep (p, bs, cs) =
      (p, bs, as.foldl (fun acc a => addCoeffLists (bs.map (mulReduce p a)) (zeroBits p :: acc)) cs) := by
  induction as generalizing cs with
  | nil => rfl
  | cons a as ih => exact ih _

def mulStepProg : PolyTimeFun (MulState × BitStr) MulState :=
  let p := fst.comp fst
  let bs := fst.comp (snd.comp fst)
  let cs := snd.comp (snd.comp fst)
  let a := snd
  congr (p.pair (bs.pair (addCoeffListsProg.comp
    ((scaleCoeffProg.comp (bs.pair (p.pair a))).pair (cons (zeroBitsProg.comp p) cs)))))
    (fun q => mulStep q.1 q.2) (by
      rintro ⟨⟨p, bs, cs⟩, a⟩
      change (p, bs, addCoeffLists (scaleCoeffProg (bs, p, a)) (zeroBits p :: cs)) = _
      rfl)

theorem mulStep_bounded : FoldBounded mulStepProg (20 * X ^ 2 + 20 * X + 20) := by
  intro as s pre post heq
  rcases s with ⟨p, bs, cs⟩
  let N := esize (as, p, bs, cs)
  have hs : N = esize as + esize p + esize bs + esize cs + 3 := by simp [N, esize_prod]; omega
  have hp : p.length ≤ N := by have := length_le_esize_bitStr p; omega
  have hb : bs.length ≤ N := by have := length_le_esize_list bs; omega
  have hc : cs.length ≤ N := by have := length_le_esize_list cs; omega
  have hpre : pre.length ≤ N := by
    have := length_le_esize_list as
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  have ha : ∀ a ∈ pre, a.length ≤ N := by
    intro a ha
    have hm : a ∈ as := by rw [heq]; exact List.mem_append_left _ ha
    have h₁ := esize_mem_le hm
    have h₂ := length_le_esize_bitStr a
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    omega
  have hshape := fold_mulStep_shape pre p bs cs
  have hsize := esize_coefficients_le _ N (fold_mulStep_width pre p bs cs N hp ha hw)
  have hn : (pre.foldl mulStep (p, bs, cs)).2.2.length ≤ 3 * N := by omega
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl mulStep (p, bs, cs)) ≤ _
  rw [esize_prod, esize_prod, hshape.1, hshape.2.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + (esize bs + esize (pre.foldl mulStep (p, bs, cs)).2.2 + 1) + 1 ≤
    20 * N ^ 2 + 20 * N + 20
  nlinarith

/-- A globally polynomial-time product of two supplied-quotient coefficient lists. -/
def mulCoeffListsProg : PolyTimeFun (BitStr × List BitStr × List BitStr) (List BitStr) :=
  let scan := foldl mulStepProg (20 * X ^ 2 + 20 * X + 20) mulStep_bounded
  congr ((snd.comp snd).comp (scan.comp
    ((PolyTimeFun.reverse.comp (fst.comp snd)).pair (fst.pair ((snd.comp snd).pair (const []))))))
    (fun q => mulCoeffLists q.1 q.2.1 q.2.2) (by
      rintro ⟨p, as, bs⟩
      change (as.reverse.foldl mulStep (p, bs, [])).2.2 = _
      rw [fold_mulStep_eq, List.foldl_reverse]
      induction as with
      | nil => rfl
      | cons a as ih =>
        dsimp only at ih ⊢
        simp only [List.foldr_cons, mulCoeffLists, ih])

@[simp] theorem mulCoeffListsProg_apply (p : BitStr) (as bs : List BitStr) :
    mulCoeffListsProg (p, as, bs) = mulCoeffLists p as bs := rfl

end MIPRE.LowDegree.BinaryQuotient

end


