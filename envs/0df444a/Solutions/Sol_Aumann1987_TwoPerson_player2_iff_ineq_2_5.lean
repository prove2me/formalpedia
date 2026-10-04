-- Prove2me | solution 1 for Aumann1987.TwoPerson.player2_iff_ineq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:43:01.596891+00:00
-- url     : https://prove2.me/submissions/4aefee3b-60e4-4712-b945-979b3423c299

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
    (h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (hp : Aumann1987.TwoPerson.IsDistribution p) :
    Aumann1987.TwoPerson.DevCond₂ h₂ p ↔
      ∀ k r : S₂, 0 ≤ ∑ j, (h₂ j k - h₂ j r) * p j k := by
  classical
  constructor
  · -- (2.2) on distributions implies (2.5): test the deviation changing only `k` to `r`
    intro hdev k r
    have key0 := hdev (fun y => if y = k then r else y)
    have h1 : (∑ j, ∑ y, p j y * h₂ j (if y = k then r else y))
        = ∑ y, ∑ j, p j y * h₂ j (if y = k then r else y) := Finset.sum_comm
    have h2 : (∑ j, ∑ y, p j y * h₂ j y)
        = ∑ y, ∑ j, p j y * h₂ j y := Finset.sum_comm
    rw [h1, h2] at key0
    have key := key0
    have hG : ∀ y ∈ Finset.univ,
        ∑ j, p j y * h₂ j (if y = k then r else y)
          = if y = k then ∑ j, p j k * h₂ j r else ∑ j, p j y * h₂ j y := by
      intro y _
      by_cases hy : y = k <;> simp [hy]
    have lhs : ∑ y, ∑ j, p j y * h₂ j (if y = k then r else y)
        = ∑ j, p j k * h₂ j r + (∑ y ∈ Finset.univ.erase k, ∑ j, p j y * h₂ j y) := by
      rw [Finset.sum_congr rfl hG, sum_split]
    have rhs : ∑ y, ∑ j, p j y * h₂ j y
        = ∑ j, p j k * h₂ j k + (∑ y ∈ Finset.univ.erase k, ∑ j, p j y * h₂ j y) := by
      rw [← Finset.add_sum_erase Finset.univ (fun y => ∑ j, p j y * h₂ j y)
        (Finset.mem_univ k)]
    have rearr : ∑ j, (h₂ j k - h₂ j r) * p j k
        = (∑ j, p j k * h₂ j k) - (∑ j, p j k * h₂ j r) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith [key, lhs, rhs, rearr]
  · -- (2.5) implies (2.2) on distributions: sum the pointwise inequalities
    intro hineq ψ
    have : ∀ y ∈ Finset.univ,
        ∑ j, p j y * h₂ j (ψ y) ≤ ∑ j, p j y * h₂ j y := by
      intro y _
      have h2 : ∑ j, (h₂ j y - h₂ j (ψ y)) * p j y
          = (∑ j, p j y * h₂ j y) - (∑ j, p j y * h₂ j (ψ y)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have h3 := hineq y (ψ y)
      linarith
    calc ∑ j, ∑ k, p j k * h₂ j (ψ k)
        = ∑ k, ∑ j, p j k * h₂ j (ψ k) := Finset.sum_comm
      _ ≤ ∑ k, ∑ j, p j k * h₂ j k := Finset.sum_le_sum this
      _ = ∑ j, ∑ k, p j k * h₂ j k := Finset.sum_comm
