-- Prove2me | solution 1 for AlgMechDesign.Additive.claim_4_11
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:02:04.605374+00:00
-- url     : https://prove2.me/submissions/a59d4a48-1e8e-4bcf-9a5c-72a5a2d16ede

import Theorems.Thm_AlgMechDesign_Additive_maximization

set_option autoImplicit false
open AlgMechDesign.Additive Finset

private theorem price_update {n k : ℕ}
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (X : Finset (Fin k))
    (t : Fin n → Fin k → ℝ) (r : Fin k → ℝ) :
    price alloc pay i X (Function.update t i r) = price alloc pay i X t := by
  classical
  have hp : (fun z : Fin k → ℝ => IsAgentType z ∧
      taskSet (alloc (Function.update (Function.update t i r) i z)) i = X) =
      (fun z : Fin k → ℝ => IsAgentType z ∧ taskSet (alloc (Function.update t i z)) i = X) := by
    funext z
    rw [Function.update_idem]
  unfold price IsAttainable
  change (if h : ∃ z, (fun z : Fin k → ℝ => IsAgentType z ∧
    taskSet (alloc (Function.update (Function.update t i r) i z)) i = X) z then _ else _) = _
  simp_rw [hp, Function.update_idem]

private theorem attainable_of_price_ne_zero {n k : ℕ}
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (X : Finset (Fin k))
    (t : Fin n → Fin k → ℝ) (h : price alloc pay i X t ≠ 0) :
    IsAttainable alloc i t X := by
  by_contra hn
  simp [price, hn] at h

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hadd : IsAdditive alloc pay) (i : Fin n)
    (hempty : IsAttainable alloc i (fun _ _ => (1 : ℝ)) ∅)
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    taskSet (alloc (fun _ _ => (1 : ℝ))) i ⊆
      taskSet (alloc (Function.update (fun _ _ => (1 : ℝ)) i
        (fun j => if j ∈ taskSet (alloc (fun _ _ => (1 : ℝ))) i then 1 - ε else ε))) i := by
  classical
  let t : Fin n → Fin k → ℝ := fun _ _ => 1
  let X := taskSet (alloc t) i
  let u := Function.update t i (fun j => if j ∈ X then 1 - ε else ε)
  let Y := taskSet (alloc u) i
  have ht : IsType t := by intro l j; norm_num [t]
  have hu : IsType u := by
    intro l j
    by_cases hl : l = i
    · simp only [u, hl, Function.update_self]
      split_ifs <;> linarith
    · simp [u, hl, t]
  have hemptyU : IsAttainable alloc i u ∅ := by
    simpa [u, IsAttainable, Function.update_idem] using hempty
  have hzero : ∀ v, IsType v → price alloc pay i ∅ v = 0 := by
    intro v hv
    simpa using hadd i v hv ∅
  have hXpay : (X.card : ℝ) ≤ price alloc pay i X t := by
    have h := maximization alloc pay htr t ht i ∅ hempty
    rw [hzero t ht] at h
    simpa [t, X] using h
  have hsingle : ∀ j ∈ X, 1 ≤ price alloc pay i {j} t := by
    intro j hj
    by_contra h
    have hjprice : price alloc pay i {j} t < 1 := lt_of_not_ge h
    have hsplit : price alloc pay i (X.erase j) t + price alloc pay i {j} t = price alloc pay i X t := by
      rw [hadd i t ht (X.erase j), hadd i t ht X]
      exact Finset.sum_erase_add X (fun q => price alloc pay i {q} t) hj
    have hcard : (1 : ℝ) ≤ X.card := by exact_mod_cast Finset.one_le_card.mpr ⟨j, hj⟩
    have hpos : 0 < price alloc pay i (X.erase j) t := by linarith
    have hatt := attainable_of_price_ne_zero alloc pay i (X.erase j) t (ne_of_gt hpos)
    have hm := maximization alloc pay htr t ht i (X.erase j) hatt
    have hce : ((X.erase j).card : ℝ) + 1 = X.card := by
      exact_mod_cast Finset.card_erase_add_one hj
    change price alloc pay i (X.erase j) t - ∑ q ∈ X.erase j, (1 : ℝ) ≤
      price alloc pay i X t - ∑ q ∈ X, (1 : ℝ) at hm
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hm
    linarith
  have hYpay : 0 ≤ price alloc pay i Y u := by
    have h := maximization alloc pay htr u hu i ∅ hemptyU
    rw [hzero u hu] at h
    simp only [Finset.sum_empty, sub_zero] at h
    have hc : 0 ≤ ∑ j ∈ Y, u i j := Finset.sum_nonneg (fun j hj => le_of_lt (hu i j))
    change 0 ≤ price alloc pay i Y u - ∑ j ∈ Y, u i j at h
    linarith
  change X ⊆ Y
  intro j hj
  by_contra hjY
  have hsj : 1 ≤ price alloc pay i {j} u := by
    rw [show price alloc pay i {j} u = price alloc pay i {j} t from price_update alloc pay i {j} t _]
    exact hsingle j hj
  have hsplit : price alloc pay i (insert j Y) u = price alloc pay i {j} u + price alloc pay i Y u := by
    rw [hadd i u hu (insert j Y), hadd i u hu Y, Finset.sum_insert hjY]
  have hpos : 0 < price alloc pay i (insert j Y) u := by linarith
  have hatt := attainable_of_price_ne_zero alloc pay i (insert j Y) u (ne_of_gt hpos)
  have hm := maximization alloc pay htr u hu i (insert j Y) hatt
  change price alloc pay i (insert j Y) u - ∑ q ∈ insert j Y, u i q ≤
    price alloc pay i Y u - ∑ q ∈ Y, u i q at hm
  rw [hsplit, Finset.sum_insert hjY] at hm
  have htime : u i j = 1 - ε := by simp [u, hj]
  rw [htime] at hm
  linarith

