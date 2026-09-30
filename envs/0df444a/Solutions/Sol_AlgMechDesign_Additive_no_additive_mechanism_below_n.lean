-- Prove2me | solution 1 for AlgMechDesign.Additive.no_additive_mechanism_below_n
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:06:04.472231+00:00
-- url     : https://prove2.me/submissions/bd376767-e9e1-471b-9b51-1321a756c145

import Theorems.Thm_AlgMechDesign_Additive_maximization
import Theorems.Thm_AlgMechDesign_Additive_exists_agent_many_tasks
import Theorems.Thm_AlgMechDesign_Additive_ratio_step

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

private theorem keep_tasks {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hadd : IsAdditive alloc pay) (i : Fin n)
    (hempty : IsAttainable alloc i (fun _ _ => (1 : ℝ)) ∅)
    (r : Fin k → ℝ) (hrpos : IsAgentType r)
    (hrlow : ∀ j ∈ taskSet (alloc (fun _ _ => (1 : ℝ))) i, r j < 1) :
    taskSet (alloc (fun _ _ => (1 : ℝ))) i ⊆
      taskSet (alloc (Function.update (fun _ _ => (1 : ℝ)) i r)) i := by
  classical
  let t : Fin n → Fin k → ℝ := fun _ _ => 1
  let X := taskSet (alloc t) i
  let u := Function.update t i r
  let Y := taskSet (alloc u) i
  have ht : IsType t := by intro l j; norm_num [t]
  have hu : IsType u := by
    intro l j
    by_cases hl : l = i
    · simpa [u, hl] using hrpos j
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
  have htime : u i j < 1 := by simpa [u] using hrlow j hj
  linarith

private theorem empty_attainable {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (c : ℝ) (hc : 0 ≤ c) (happ : IsApprox c alloc) (i : Fin n) :
    IsAttainable alloc i (fun _ _ => (1 : ℝ)) ∅ := by
  classical
  have hne : (univ.erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := hne
  have hai := (Finset.mem_erase.mp ha).1
  let M : ℝ := c * k + 1
  let u : Fin n → Fin k → ℝ := Function.update (fun _ _ => 1) i (fun _ => M)
  have hM : 0 < M := by dsimp [M]; positivity
  have hu : IsType u := by
    intro l j
    by_cases he : l = i
    · simpa [u, he] using hM
    · simp [u, he]
  have hcompare : makespan u (fun _ => a) ≤ k := by
    unfold makespan
    apply Finset.sup'_le
    intro l hl
    by_cases he : l = a
    · simp [load, taskSet, u, he, hai]
    · simpa [load, taskSet, Ne.symm he] using (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hbound : makespan u (alloc u) ≤ c * k :=
    (happ u hu (fun _ => a)).trans (mul_le_mul_of_nonneg_left hcompare hc)
  refine ⟨fun _ => M, fun _ => hM, ?_⟩
  change taskSet (alloc u) i = ∅
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have he : alloc u j = i := (Finset.mem_filter.mp hj).2
  have hload : M ≤ load u (alloc u) i := by
    have hterm : u i j = M := by simp [u]
    calc
      M = u i j := hterm.symm
      _ ≤ load u (alloc u) i :=
        Finset.single_le_sum (fun q hq => le_of_lt (hu i q)) hj
  have hlarge := hload.trans (Finset.le_sup' (load u (alloc u)) (Finset.mem_univ _))
  dsimp [M] at hlarge
  change c * k + 1 ≤ makespan u (alloc u) at hlarge
  linarith

theorem solution {n k : ℕ} [NeZero n] (hk : n ^ 2 ≤ k)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hadd : IsAdditive alloc pay) (c : ℝ) (hc : c < n) :
    ¬ IsApprox c alloc := by
  classical
  intro happ
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hkpos : 0 < k := by nlinarith
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  let t : Fin n → Fin k → ℝ := fun _ _ => 1
  have ht : IsType t := by intro l j; norm_num [t]
  let j₀ : Fin k := ⟨0, hkpos⟩
  have hone : (1 : ℝ) ≤ makespan t (alloc t) := by
    have hload : (1 : ℝ) ≤ load t (alloc t) (alloc t j₀) := by
      have hterm : t (alloc t j₀) j₀ = 1 := rfl
      calc
        1 = t (alloc t j₀) j₀ := hterm.symm
        _ ≤ load t (alloc t) (alloc t j₀) :=
          Finset.single_le_sum (fun q hq => le_of_lt (ht (alloc t j₀) q))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    exact hload.trans (Finset.le_sup' (load t (alloc t)) (Finset.mem_univ _))
  have hc1 : 1 ≤ c := by
    have hself := happ t ht (alloc t)
    nlinarith
  have hn2 : 2 ≤ n := by
    have hr : (1 : ℝ) < n := lt_of_le_of_lt hc1 hc
    have hnat : 1 < n := by exact_mod_cast hr
    omega
  obtain ⟨i, hi⟩ := exists_agent_many_tasks hk (alloc t)
  obtain ⟨x, hxsub, hxcard⟩ := Finset.exists_subset_card_eq hi
  have hden : 0 < 2 * ((n : ℝ) + c * k) := by positivity
  let ε : ℝ := ((n : ℝ) - c) / (2 * ((n : ℝ) + c * k))
  have hε₀ : 0 < ε := div_pos (sub_pos.mpr hc) hden
  have hε₁ : ε < 1 := by
    apply (div_lt_iff₀ hden).mpr
    have hck : 0 ≤ c * (k : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    nlinarith
  have heq : ε * (2 * ((n : ℝ) + c * k)) = (n : ℝ) - c := by
    dsimp [ε]
    field_simp
  let r : Fin k → ℝ := fun j => if j ∈ x then 1 - ε else ε
  have hr : IsAgentType r := by intro j; dsimp [r]; split_ifs <;> linarith
  have hrlow : ∀ j ∈ taskSet (alloc t) i, r j < 1 := by
    intro j hj
    dsimp [r]
    split_ifs <;> linarith
  have hkeep := keep_tasks alloc pay htr hadd i
    (empty_attainable hn2 alloc c (by linarith) happ i) r hr hrlow
  have hratio := ratio_step i x hxcard ε hε₀ hε₁
  obtain ⟨y, hy⟩ := hratio.2
  let u := Function.update t i r
  have hu : IsType u := by
    intro l j
    by_cases he : l = i
    · simpa [u, he] using hr j
    · simp [u, he, t]
  have hlo : (1 - ε) * n ≤ makespan u (alloc u) :=
    hratio.1 (alloc u) (hxsub.trans hkeep)
  have hhi := (happ u hu y).trans (mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ c))
  nlinarith

