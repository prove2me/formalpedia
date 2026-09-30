-- Prove2me | solution 1 for AlgMechDesign.LowerBound.claim_4_8
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:10:13.717612+00:00
-- url     : https://prove2.me/submissions/64a30872-7700-44c8-8bcc-528fbb3ba3f7

import Definitions.Def_AlgMechDesign_LowerBound_Model

set_option autoImplicit false
open AlgMechDesign.LowerBound Finset

theorem solution {k : ℕ} (hk : 3 ≤ k) (alloc : (Fin 2 → Fin k → ℝ) → (Fin k → Fin 2))
    (pay : (Fin 2 → Fin k → ℝ) → Fin 2 → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin 2 → Fin k → ℝ) (ht : t = fun _ _ => 1)
    (hcard : (taskSet (alloc t) 0).card ≤ (taskSet (alloc t) 1).card)
    (x : Finset (Fin k)) (hx : x = taskSet (alloc t) 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (that : Fin 2 → Fin k → ℝ)
    (hthat : that = Function.update t 0 (fun j => if j ∈ x then ε else 1 + ε)) :
    alloc that = alloc t := by
  classical
  have htpos : IsType t := by intro l j; simp [ht]
  have hup : Function.update t 0 (that 0) = that := by
    rw [hthat]
    simp
  have hdown : Function.update that 0 (t 0) = t := by
    rw [hthat, Function.update_idem, Function.update_eq_self]
  have hu : IsType that := by
    intro l j
    by_cases he : l = 0
    · simp [hthat, he]
      split_ifs <;> linarith
    · simp [hthat, he, ht]
  have h₁ := htruth t htpos 0 (t 0) (that 0) (htpos 0) (hu 0)
  have h₂ := htruth that hu 0 (that 0) (t 0) (hu 0) (htpos 0)
  simp only [Function.update_eq_self, hup, hdown, utility, taskTime] at h₁ h₂
  have hg : ∀ z : Fin k → Fin 2,
      (∑ j, if z j = 0 then 1 - that 0 j else 0) =
        (∑ j ∈ taskSet z 0, (1 : ℝ)) - ∑ j ∈ taskSet z 0, that 0 j := by
    intro z
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_filter (fun j => z j = 0) (fun j => 1 - that 0 j)).symm
  have hgain : (∑ j, if alloc t j = 0 then 1 - that 0 j else 0) ≤
      ∑ j, if alloc that j = 0 then 1 - that 0 j else 0 := by
    rw [hg, hg]
    have ht0 : t 0 = fun _ => 1 := by rw [ht]
    simp only [ht0] at h₁
    linarith
  have htime : ∀ j, that 0 j = if alloc t j = 0 then ε else 1 + ε := by
    intro j
    simp [hthat, hx, taskSet]
  by_contra hne
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hne
  have hstrict : (∑ j, if alloc that j = 0 then 1 - that 0 j else 0) <
      ∑ j, if alloc t j = 0 then 1 - that 0 j else 0 := by
    apply Finset.sum_lt_sum
    · intro j hj
      rw [htime]
      by_cases hnew : alloc that j = 0 <;> by_cases hold : alloc t j = 0 <;>
        simp [hnew, hold] <;> linarith
    · refine ⟨j₀, Finset.mem_univ _, ?_⟩
      rw [htime]
      have hne0 : (alloc that j₀ = 0) ≠ (alloc t j₀ = 0) := by
        intro he
        have hn : alloc that j₀ = 0 ∨ alloc that j₀ = 1 := by omega
        have ho : alloc t j₀ = 0 ∨ alloc t j₀ = 1 := by omega
        rcases hn with hn | hn <;> rcases ho with ho | ho <;> simp_all
      by_cases hnew : alloc that j₀ = 0 <;> by_cases hold : alloc t j₀ = 0 <;>
        simp_all <;> linarith
  linarith
