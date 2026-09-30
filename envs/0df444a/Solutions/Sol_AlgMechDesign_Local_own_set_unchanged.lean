-- Prove2me | solution 1 for AlgMechDesign.Local.own_set_unchanged
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:14:13.164895+00:00
-- url     : https://prove2.me/submissions/6c7046e3-2b62-4008-bfd9-2e682be159be

import Theorems.Thm_AlgMechDesign_Local_maximization

set_option autoImplicit false
open AlgMechDesign.Local Finset

private theorem price_update {n k : ℕ}
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (X : Finset (Fin k))
    (t : Fin n → Fin k → ℝ) (r : Fin k → ℝ) :
    price alloc pay i X (Function.update t i r) = price alloc pay i X t := by
  classical
  have hp : (fun z : Fin k → ℝ => IsAgentType z ∧
      agentSet alloc (Function.update (Function.update t i r) i z) i = X) =
      (fun z : Fin k → ℝ => IsAgentType z ∧ agentSet alloc (Function.update t i z) i = X) := by
    funext z
    rw [Function.update_idem]
  unfold price IsAttainable
  change (if h : ∃ z, (fun z : Fin k → ℝ => IsAgentType z ∧
    agentSet alloc (Function.update (Function.update t i r) i z) i = X) z then _ else _) = _
  simp_rw [hp, Function.update_idem]

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n)
    (huniq : IsUniqueMaximizer alloc pay t i) (ε : ℝ) (hε : 0 < ε)
    (hle : ∀ j ∈ agentSet alloc t i, ε ≤ t i j) :
    agentSet alloc (setTimes t i (agentSet alloc t i) ε) i = agentSet alloc t i := by
  classical
  let X := agentSet alloc t i
  let r : Fin k → ℝ := fun j => if j ∈ X then ε else t i j
  let u := Function.update t i r
  let Y := agentSet alloc u i
  have hr : IsAgentType r := by
    intro j
    dsimp [r]
    split_ifs
    · exact hε
    · exact ht i j
  have hu : IsType u := by
    intro l j
    by_cases he : l = i
    · simpa [u, he] using hr j
    · simpa [u, he] using ht l j
  have hYatt : IsAttainable alloc i Y t := ⟨r, hr, rfl⟩
  have hXatt : IsAttainable alloc i X u := by
    refine ⟨t i, ht i, ?_⟩
    simp [u, Function.update_idem, X]
  change Y = X
  by_contra hne
  have hstrict := huniq Y hYatt hne
  have hmax := (maximization alloc pay htr u hu i).2 X hXatt
  change price alloc pay i Y t - setTime (t i) Y < price alloc pay i X t - setTime (t i) X at hstrict
  change price alloc pay i X u - setTime (u i) X ≤ price alloc pay i Y u - setTime (u i) Y at hmax
  rw [show price alloc pay i X u = price alloc pay i X t from price_update alloc pay i X t r,
    show price alloc pay i Y u = price alloc pay i Y t from price_update alloc pay i Y t r] at hmax
  let credit : Fin k → ℝ := fun j => if j ∈ X then t i j - ε else 0
  have hc : ∀ j, 0 ≤ credit j := by
    intro j
    dsimp [credit]
    split_ifs with hj
    · exact sub_nonneg.mpr (hle j hj)
    · exact le_rfl
  have hdiff : ∀ Z : Finset (Fin k), setTime (t i) Z - setTime (u i) Z = ∑ j ∈ Z, credit j := by
    intro Z
    unfold setTime
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [u, r, credit]
    simp only [Function.update_self]
    split_ifs <;> ring
  have hfull : ∑ j, credit j = ∑ j ∈ X, credit j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ X)
    intro j hj hjX
    simp [credit, hjX]
  have hcredits : ∑ j ∈ Y, credit j ≤ ∑ j ∈ X, credit j := by
    rw [← hfull]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Y) (fun j hj hjY => hc j)
  rw [← hdiff Y, ← hdiff X] at hcredits
  linarith
