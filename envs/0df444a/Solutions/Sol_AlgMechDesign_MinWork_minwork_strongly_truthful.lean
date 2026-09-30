-- Prove2me | solution 1 for AlgMechDesign.MinWork.minwork_strongly_truthful
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:37:50.824502+00:00
-- url     : https://prove2.me/submissions/5e573952-4e28-4533-9bb3-bbd3df6a6a20

import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

set_option autoImplicit false
open AlgMechDesign.MinWork Finset

private theorem best_update {n k : ℕ} (hn : 2 ≤ n)
    (d : Fin n → Fin k → ℝ) (i : Fin n) (r : Fin k → ℝ) (j : Fin k) :
    secondBest hn (Function.update d i r) i j = secondBest hn d i j := by
  unfold secondBest
  apply Finset.inf'_congr (erase_nonempty hn i) rfl
  intro l hl
  simp [(Finset.mem_erase.mp hl).1]

private theorem utility_sum {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (i : Fin n) (r ti : Fin k → ℝ) :
    utility alloc (minWorkPay hn alloc) (Function.update d i r) i ti =
      ∑ j, if alloc (Function.update d i r) j = i then secondBest hn d i j - ti j else 0 := by
  unfold utility minWorkPay
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  simp only [best_update]

private theorem own_le {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (d : Fin n → Fin k → ℝ) (i : Fin n) (r : Fin k → ℝ) (j : Fin k)
    (hown : alloc (Function.update d i r) j = i) : r j ≤ secondBest hn d i j := by
  rw [← best_update hn d i r j]
  apply Finset.le_inf' (erase_nonempty hn i)
  intro l hl
  simpa [hown] using hmin (Function.update d i r) j l

private theorem other_le {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (d : Fin n → Fin k → ℝ) (i : Fin n) (r : Fin k → ℝ) (j : Fin k)
    (hown : alloc (Function.update d i r) j ≠ i) : secondBest hn d i j ≤ r j := by
  rw [← best_update hn d i r j]
  have hbest : secondBest hn (Function.update d i r) i j ≤
      (Function.update d i r) (alloc (Function.update d i r) j) j :=
    Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hown, Finset.mem_univ _⟩)
  have halloc := hmin (Function.update d i r) j i
  simpa using hbest.trans halloc

private theorem truthful_gain {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (d : Fin n → Fin k → ℝ) (i : Fin n) (ti : Fin k → ℝ) (j : Fin k) :
    (if alloc (Function.update d i ti) j = i then secondBest hn d i j - ti j else 0) =
      max (secondBest hn d i j - ti j) 0 := by
  by_cases h : alloc (Function.update d i ti) j = i
  · rw [if_pos h, max_eq_left]
    exact sub_nonneg.mpr (own_le hn alloc hmin d i ti j h)
  · rw [if_neg h, max_eq_right]
    exact sub_nonpos.mpr (other_le hn alloc hmin d i ti j h)

theorem solution {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsStronglyTruthful alloc (minWorkPay hn alloc) := by
  have hpoint : ∀ (d : Fin n → Fin k → ℝ) (i : Fin n) (ti r : Fin k → ℝ) (j : Fin k),
      (if alloc (Function.update d i r) j = i then secondBest hn d i j - ti j else 0) ≤
        (if alloc (Function.update d i ti) j = i then secondBest hn d i j - ti j else 0) := by
    intro d i ti r j
    rw [truthful_gain hn alloc hmin]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  constructor
  · intro d hd i ti r hti hr
    rw [utility_sum, utility_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact hpoint d i ti r j
  · intro i ti r hti hr hne
    let d : Fin n → Fin k → ℝ := fun _ j => (ti j + r j) / 2
    have hd : IsType d := by
      intro l j
      dsimp [d]
      linarith [hti j, hr j]
    have hb : ∀ j, secondBest hn d i j = (ti j + r j) / 2 := by
      intro j
      simp [secondBest, d]
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hne
    refine ⟨d, hd, ?_⟩
    rw [utility_sum, utility_sum]
    apply Finset.sum_lt_sum
    · intro j hj
      exact hpoint d i ti r j
    · refine ⟨j₀, Finset.mem_univ _, ?_⟩
      rcases lt_or_gt_of_ne hj₀ with hlt | hgt
      · have hr_own : alloc (Function.update d i r) j₀ = i := by
          by_contra h
          have hle := other_le hn alloc hmin d i r j₀ h
          rw [hb] at hle
          linarith
        have ht_other : alloc (Function.update d i ti) j₀ ≠ i := by
          intro h
          have hle := own_le hn alloc hmin d i ti j₀ h
          rw [hb] at hle
          linarith
        rw [if_pos hr_own, if_neg ht_other, hb]
        linarith
      · have ht_own : alloc (Function.update d i ti) j₀ = i := by
          by_contra h
          have hle := other_le hn alloc hmin d i ti j₀ h
          rw [hb] at hle
          linarith
        have hr_other : alloc (Function.update d i r) j₀ ≠ i := by
          intro h
          have hle := own_le hn alloc hmin d i r j₀ h
          rw [hb] at hle
          linarith
        rw [if_neg hr_other, if_pos ht_own, hb]
        linarith
