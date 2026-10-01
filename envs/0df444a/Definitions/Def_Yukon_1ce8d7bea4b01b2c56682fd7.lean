-- Prove2me | Definitions.Def_Yukon_1ce8d7bea4b01b2c56682fd7
-- name    : Yukon_1ce8d7bea4b01b2c56682fd7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:29:40.187863+00:00
-- url     : https://prove2.me/theorems/5102a241-5a9a-4f07-8362-83bca443e893
-- title:
--   YukonModule.CompPoly.Univariate.ToPoly.Equiv.part0
-- statement:
--   Source module CompPoly.Univariate.ToPoly.Equiv.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Univariate/ToPoly/Equiv.lean
--
--   yukon-proof-operation:64ad0c00fb8527972286f2fdce6e79560671b171b49d1b01bc556dc57678c650
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNDJhMDA3YTFmMTExYjJlNjk1YWUwNmJhZDg2NDcxOTg4MzgwZDUxYmY0NTQ3OTlmODdjMjA1OGI5ZTAwZGE3OCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjY0YWQwYzAwZmI4NTI3OTcyMjg2ZjJmZGNlNmU3OTU2MDY3MWIxNzFiNDlkMWIwMWJjNTU2ZGM1NzY3OGM2NTAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8xY2U4ZDdiZWE0YjAxYjJjNTY2ODJmZDciLCJ2IjoyfQ]

/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
module

import all Definitions.Def_Yukon_f30e622756f509503260ecf4

public import Definitions.Def_Yukon_f30e622756f509503260ecf4



public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Cases
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.GroupWithZero.Nat
public import Init
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Polynomial.Inductions
meta import Definitions.Def_Yukon_f30e622756f509503260ecf4
set_option backward.isDefEq.respectTransparency.types false
/-!
# `toPoly` Equivalence

Ring equivalences between computable univariate polynomials and `Polynomial`.
-/

public section

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*} [Semiring R] [BEq R]

section RingEquiv

@[grind =]
lemma Raw.toPoly_neg {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    (-p).toPoly = -p.toPoly := by
  ext i
  rw [Polynomial.coeff_neg, Raw.coeff_toPoly, Raw.coeff_toPoly]
  change p.neg.coeff i = -p.coeff i
  exact Raw.neg_coeff p i

@[grind =]
lemma toPoly_neg {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (-p).toPoly = -p.toPoly := by
  exact Raw.toPoly_neg p.val

@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  apply Raw.toPoly_add

@[grind =]
lemma Raw.toPoly_sub {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial.Raw R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  change (p + -q).toPoly = p.toPoly + -q.toPoly
  rw [Raw.toPoly_add, Raw.toPoly_neg]

@[grind =]
lemma toPoly_sub {R : Type*} [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  change (p + -q).toPoly = p.toPoly + -q.toPoly
  rw [toPoly_add, toPoly_neg]

@[grind =]
lemma Raw.toPoly_mul_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (i : ℕ) :
    (p * q).toPoly.coeff i = (p.toPoly * q.toPoly).coeff i := by
  rw [coeff_toPoly, mul_coeff, Polynomial.coeff_mul]; simp
  have h_antidiagonal :
      Finset.HasAntidiagonal.antidiagonal i =
      Finset.image (fun x => (x, i - x)) (Finset.range (i + 1)) := by
    exact Finset.Nat.antidiagonal_eq_image i
  simp [h_antidiagonal ]
  have h_coeff : ∀ x, p.toPoly.coeff x = p[x]?.getD 0 ∧ q.toPoly.coeff x = q[x]?.getD 0 := by
    intro x
    repeat rw [coeff_toPoly]
    constructor <;> simp
  refine Finset.sum_congr rfl ?_
  intro x hx
  rcases h_coeff x with ⟨hp, _hq⟩
  rcases h_coeff (i - x) with ⟨_, hq⟩
  simp [hp, hq]

@[grind =]
lemma Raw.toPoly_mul [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  ext i
  exact Raw.toPoly_mul_coeff p q i

@[grind =]
lemma toPoly_mul_coeffC [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p.val * q.val).toPoly.coeff i = (p.val.toPoly * q.val.toPoly).coeff i := by
  simpa using Raw.toPoly_mul_coeff p.val q.val i

@[grind =]
lemma toPoly_mul [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  exact Raw.toPoly_mul p.val q.val

@[simp, grind =]
lemma eval₂_C {R : Type*} [Semiring R] {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (r : R) :
    (Raw.C r).eval₂ f x = f r := by
  unfold CPolynomial.Raw.eval₂ Raw.C
  ring_nf
  simp [Array.zipIdx]

@[simp, grind =]
lemma Raw.toPoly_C {R : Type*} [Semiring R] (r : R) :
    (Raw.C r).toPoly = Polynomial.C r := by
  unfold Raw.toPoly
  exact eval₂_C Polynomial.C Polynomial.X r

@[simp, grind =]
lemma Raw.toPoly_one {R : Type*} [Semiring R] :
    (1 : CPolynomial.Raw R).toPoly = 1 := by
  have : (1 : CPolynomial.Raw R).toPoly = (Raw.C 1).toPoly := by rfl
  apply this.trans; clear this
  apply toPoly_C

lemma toPoly_one [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).toPoly = 1 := by
  apply Raw.toPoly_one

@[grind =]
lemma Raw.toPoly_pow [LawfulBEq R] (p : CPolynomial.Raw R) :
    ∀ n : ℕ, (p ^ n).toPoly = p.toPoly ^ n
  | 0 => by
      simp [Raw.pow_zero]
  | n + 1 => by
      rw [Raw.pow_succ, Raw.toPoly_mul, Raw.toPoly_pow p n]
      simp [pow_succ']

@[simp, grind =]
lemma Raw.toPoly_zero {R : Type*} [Semiring R] : (0 : CPolynomial.Raw R).toPoly = 0 := by
  simp [Raw.toPoly, Raw.eval₂]

lemma toPoly_zero {R : Type*} [Semiring R] : (0 : CPolynomial R).toPoly = 0 := by
  apply Raw.toPoly_zero

@[simp, grind =]
lemma Raw.toPoly_X {R : Type*} [Semiring R] :
    (Raw.X : CPolynomial.Raw R).toPoly = Polynomial.X := by
  unfold CPolynomial.Raw.X
  simp [Raw.toPoly, Raw.eval₂]

@[grind =]
lemma toPoly_pow [Nontrivial R] [LawfulBEq R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := by
  change (p ^ n).val.toPoly = p.val.toPoly ^ n
  rw [val_pow]
  exact Raw.toPoly_pow p.val n

lemma toPoly_sum.{u} {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] {ι : Type u}
    [DecidableEq ι]
    {s : Finset ι} {f : ι → CPolynomial R} :
      (∑ j ∈ s, f j).toPoly = ∑ j ∈ s, ((f j).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (toPoly_zero (R := R))
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, toPoly_add, ih]

lemma toPoly_prod.{u} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {ι : Type u} [DecidableEq ι]
    {s : Finset ι} {f : ι → CPolynomial R} :
      (∏ j ∈ s, f j).toPoly = ∏ j ∈ s, ((f j).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [toPoly_one]
  | insert a s ha ih =>
      simp [Finset.prod_insert, ha, toPoly_mul, ih]

noncomputable def ringEquiv [LawfulBEq R] [Nontrivial R] :
  CPolynomial R ≃+* Polynomial R where
  toFun := CPolynomial.toPoly
  invFun := fun p => ⟨p.toImpl, isCanonical_toImpl p⟩
  left_inv := by
    unfold Function.LeftInverse; intro x
    apply Subtype.ext; apply toImpl_toPoly_of_canonical
  right_inv := by
    unfold Function.RightInverse CPolynomial.toPoly
    apply toPoly_toImpl
  map_mul' := by intros p q; rw [toPoly_mul p q]
  map_add' := by intros p q; apply toPoly_add

/-- The forward map of `ringEquiv` is `toPoly`. -/
@[simp]
theorem ringEquiv_apply [LawfulBEq R] [Nontrivial R] (p : CPolynomial R) :
    ringEquiv p = p.toPoly := by
  rfl

end RingEquiv

end CPolynomial

end CompPoly


