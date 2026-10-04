-- Prove2me | solution 1 for Aumann1987.TwoPerson.player1_iff_ineq_2_4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:42:49.474184+00:00
-- url     : https://prove2.me/submissions/0ac3ee13-9ea1-40d1-aff1-b66bc758fc93

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

/-! Auxiliary lemma: split a finite sum at a single point. -/
lemma sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (A : ℝ) (B : ι → ℝ) :
    ∑ x ∈ Finset.univ, (if x = j then A else B x) = A + ∑ x ∈ Finset.univ.erase j, B x := by
  classical
  rw [← Finset.add_sum_erase (s := Finset.univ) (f := fun x => if x = j then A else B x)
      (Finset.mem_univ j), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.ne_of_mem_erase hx]

theorem solution {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (h₁ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (hp : Aumann1987.TwoPerson.IsDistribution p) :
    Aumann1987.TwoPerson.DevCond₁ h₁ p ↔
      ∀ j q : S₁, 0 ≤ ∑ k, (h₁ j k - h₁ q k) * p j k := by
  classical
  constructor
  · -- (2.2) on distributions implies (2.4): test the deviation changing only `j` to `q`
    intro hdev j q
    have key := hdev (fun x => if x = j then q else x)
    have hG : ∀ x ∈ Finset.univ,
        ∑ k, p x k * h₁ (if x = j then q else x) k
          = if x = j then ∑ k, p j k * h₁ q k else ∑ k, p x k * h₁ x k := by
      intro x _
      by_cases hx : x = j <;> simp [hx]
    have lhs : ∑ x, ∑ k, p x k * h₁ (if x = j then q else x) k
        = ∑ k, p j k * h₁ q k + (∑ x ∈ Finset.univ.erase j, ∑ k, p x k * h₁ x k) := by
      rw [Finset.sum_congr rfl hG, sum_split]
    have rhs : ∑ x, ∑ k, p x k * h₁ x k
        = ∑ k, p j k * h₁ j k + (∑ x ∈ Finset.univ.erase j, ∑ k, p x k * h₁ x k) := by
      rw [← Finset.add_sum_erase Finset.univ (fun x => ∑ k, p x k * h₁ x k)
        (Finset.mem_univ j)]
    have rearr : ∑ k, (h₁ j k - h₁ q k) * p j k
        = (∑ k, p j k * h₁ j k) - (∑ k, p j k * h₁ q k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith [key, lhs, rhs, rearr]
  · -- (2.4) implies (2.2) on distributions: sum the pointwise inequalities
    intro hineq φ
    refine Finset.sum_le_sum fun x _ => ?_
    have h2 : ∑ k, (h₁ x k - h₁ (φ x) k) * p x k
        = (∑ k, p x k * h₁ x k) - (∑ k, p x k * h₁ (φ x) k) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h3 := hineq x (φ x)
    linarith
