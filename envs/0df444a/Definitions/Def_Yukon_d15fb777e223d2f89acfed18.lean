-- Prove2me | Definitions.Def_Yukon_d15fb777e223d2f89acfed18
-- name    : Yukon_d15fb777e223d2f89acfed18
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:39:51.552433+00:00
-- url     : https://prove2.me/theorems/6a82cafa-6bff-48c7-adac-9e24752d5bbe
-- title:
--   YukonModule.CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree.part0
-- statement:
--   Source module CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean
--
--   yukon-proof-operation:dc6c02c6e28c94b6c1691b50c64d6a4c2c92ed0501b3818bcd864d227499e9a1
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTBkYWRmNGUzN2IyMGVjNjUyYmQwN2M1M2E3OTQ1MmI2YmE0NWFjMzU4ZmMwMzVlOWVhODBkOTJkMzI0MTMzNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmRjNmMwMmM2ZTI4Yzk0YjZjMTY5MWI1MGM2NGQ2YTRjMmM5MmVkMDUwMWIzODE4YmNkODY0ZDIyNzQ5OWU5YTEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kMTVmYjc3N2UyMjNkMmY4OWFjZmVkMTgiLCJ2IjoyfQ]

/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Definitions.Def_Yukon_df15ca12ddf2d8e2d1b3970a

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.BigOperators


public import Mathlib.Algebra.Polynomial.Roots
public import Aesop
public import Mathlib.Algebra.Polynomial.Bivariate
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
meta import Definitions.Def_Yukon_df15ca12ddf2d8e2d1b3970a
set_option backward.isDefEq.respectTransparency.types false
/-!
# Mathlib-Facing Bivariate Weighted-Degree Helpers

This file extends `Polynomial.Bivariate` with weighted-degree algebra that is generic
and reusable across downstream protocol developments.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- The monomial `X^i Y^j` as a bivariate polynomial. -/
def monomial (i j : ℕ) : F[X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i 1)

/-- The weighted degree of a sum is at most the maximum of the weighted degrees. -/
lemma natWeightedDegree_add_le (p q : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  refine Finset.sup_le fun m hm ↦ ?_
  by_cases h : m ∈ p.support <;> by_cases h' : m ∈ q.support <;>
    simp_all only [Polynomial.mem_support_iff, coeff_add, ne_eq, le_sup_iff]
  · have h_deg : (p.coeff m + q.coeff m).natDegree ≤
        max ((p.coeff m).natDegree) ((q.coeff m).natDegree) :=
      natDegree_add_le (p.coeff m) (q.coeff m)
    cases max_cases (natDegree (p.coeff m)) (natDegree (q.coeff m)) <;>
      simp_all only [sup_of_le_left, sup_eq_left, and_self, natWeightedDegree]
    · exact Or.inl <|
        le_trans
          (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
          (Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m) <| by aesop)
    · exact Or.inr <|
        le_trans
          (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
          (Finset.le_sup (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop)
  all_goals simp_all only [not_not, add_zero, zero_add, not_false_eq_true]
  · exact Or.inl <|
      Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m) <| by aesop
  · exact Or.inr <|
      Finset.le_sup (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop
  · simp at hm

/-- The weighted degree of a sum is bounded by the supremum of the weighted degrees. -/
lemma natWeightedDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → F[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [natWeightedDegree]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact le_trans (natWeightedDegree_add_le _ _ _ _) (max_le_max le_rfl ih)

/-- The weighted degree of a scalar multiple is at most the weighted degree of the polynomial. -/
lemma natWeightedDegree_smul_le (a : F) (p : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (a • p) u v ≤ natWeightedDegree p u v := by
  simp only [natWeightedDegree, coeff_smul, Finset.sup_le_iff, Polynomial.mem_support_iff, ne_eq]
  intro b _
  exact le_trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (natDegree_smul_le a (p.coeff b)) u.zero_le)
      (mul_le_mul_of_nonneg_left le_rfl v.zero_le))
    (Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m)
      (show b ∈ p.support from by aesop))

/-- The degree of `Q(X, P(X))` is bounded by the weighted degree of `Q`,
provided `deg(P) ≤ k - 1`. -/
lemma degree_eval_le_weightedDegree (Q : F[X][Y]) (P : F[X]) (k : ℕ) (hP : P.natDegree ≤ k - 1) :
    (Q.eval P).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
  intro i hi
  by_cases hi' : Q.coeff i = 0
  · simp [hi', natWeightedDegree]
  · have hpow : (P ^ i).natDegree ≤ (k - 1) * i := by
      simpa [Nat.mul_comm] using
        (Polynomial.natDegree_pow_le_of_le (p := P) (m := k - 1) i hP)
    refine le_trans ?_
      (Finset.le_sup (f := fun m ↦ 1 * (Q.coeff m).natDegree + (k - 1) * m)
        (show i ∈ Q.support from Polynomial.mem_support_iff.mpr hi'))
    exact le_trans Polynomial.natDegree_mul_le <|
      by simpa [one_mul] using Nat.add_le_add_left hpow (Q.coeff i).natDegree

end Semiring

section NontrivialSemiring

variable [Semiring F] [Nontrivial F]

/-- The weighted degree of `X^i Y^j` is `u * i + v * j`. -/
lemma natWeightedDegree_monomial (i j u v : ℕ) :
    natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
  classical
  simp only [natWeightedDegree, monomial]
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro b hb
    simp at hb
    simp [← hb]
  · refine le_trans ?_ (Finset.le_sup
      (f := fun m ↦ u * (Polynomial.monomial j (Polynomial.monomial i 1) |>.coeff m |>.natDegree)
        + v * m) (b := j) ?_)
    all_goals norm_num [coeff_monomial]

end NontrivialSemiring

end
end Polynomial.Bivariate


