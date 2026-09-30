-- Prove2me | solution 1 for AlgMechDesign.Randomized.rbmw_strongly_truthful
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:46:00.101621+00:00
-- url     : https://prove2.me/submissions/9c0d9f35-4e3c-4b84-98f4-3de01e84569a

import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

set_option autoImplicit false
open AlgMechDesign.Randomized Finset

private noncomputable def threshold {k : ℕ} (β : ℝ) (s : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (j : Fin k) : ℝ :=
  if i = s j then β * d (other (s j)) j else β⁻¹ * d (s j) j

private theorem threshold_update {k : ℕ} (β : ℝ) (s : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (r : Fin k → ℝ) (j : Fin k) :
    threshold β s (Function.update d i r) i j = threshold β s d i j := by
  have hs : s j = 0 ∨ s j = 1 := by omega
  fin_cases i <;> rcases hs with hs | hs <;> simp [threshold, other, hs]

private theorem utility_sum {k : ℕ} (β : ℝ) (s : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (r ti : Fin k → ℝ) :
    utility (bmwAlloc β s) (bmwPay β s) (Function.update d i r) i ti =
      ∑ j, if bmwAlloc β s (Function.update d i r) j = i then threshold β s d i j - ti j else 0 := by
  unfold utility bmwPay
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  change (if _ then threshold β s (Function.update d i r) i j else 0) - _ = _
  rw [threshold_update]
  split_ifs <;> ring

private theorem own_le {k : ℕ} (β : ℝ) (hβ : 0 < β) (s : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (r : Fin k → ℝ) (j : Fin k)
    (hown : bmwAlloc β s (Function.update d i r) j = i) : r j ≤ threshold β s d i j := by
  have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hβ)
  have hs : s j = 0 ∨ s j = 1 := by omega
  fin_cases i <;> rcases hs with hs | hs <;>
    simp [bmwAlloc, threshold, other, hs] at hown ⊢
  all_goals first | exact hown | exact le_of_lt hown | (rw [inv_mul_eq_div]; apply (le_div_iff₀ hβ).mpr; nlinarith)

private theorem other_le {k : ℕ} (β : ℝ) (hβ : 0 < β) (s : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (r : Fin k → ℝ) (j : Fin k)
    (hown : bmwAlloc β s (Function.update d i r) j ≠ i) : threshold β s d i j ≤ r j := by
  have hinv : β * β⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hβ)
  have hs : s j = 0 ∨ s j = 1 := by omega
  fin_cases i <;> rcases hs with hs | hs <;>
    simp [bmwAlloc, threshold, other, hs] at hown ⊢
  all_goals first | exact hown | exact le_of_lt hown | (rw [inv_mul_eq_div]; apply (div_le_iff₀ hβ).mpr; nlinarith)

private theorem truthful_gain {k : ℕ} (β : ℝ) (hβ : 0 < β) (s : Fin k → Fin 2)
    (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (ti : Fin k → ℝ) (j : Fin k) :
    (if bmwAlloc β s (Function.update d i ti) j = i then threshold β s d i j - ti j else 0) =
      max (threshold β s d i j - ti j) 0 := by
  by_cases h : bmwAlloc β s (Function.update d i ti) j = i
  · rw [if_pos h, max_eq_left]
    exact sub_nonneg.mpr (own_le β hβ s d i ti j h)
  · rw [if_neg h, max_eq_right]
    exact sub_nonpos.mpr (other_le β hβ s d i ti j h)

private theorem bmw_strong {k : ℕ} (β : ℝ) (hβ : 1 ≤ β) (s : Fin k → Fin 2) :
    IsStronglyTruthful (bmwAlloc β s) (bmwPay β s) := by
  have hβpos : 0 < β := by linarith
  have hpoint : ∀ (d : Fin 2 → Fin k → ℝ) (i : Fin 2) (ti r : Fin k → ℝ) (j : Fin k),
      (if bmwAlloc β s (Function.update d i r) j = i then threshold β s d i j - ti j else 0) ≤
        (if bmwAlloc β s (Function.update d i ti) j = i then threshold β s d i j - ti j else 0) := by
    intro d i ti r j
    rw [truthful_gain β hβpos s]
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
    let d : Fin 2 → Fin k → ℝ := fun _ j =>
      if i = s j then ((ti j + r j) / 2) / β else β * ((ti j + r j) / 2)
    have hd : IsType d := by
      intro l j
      have hp : 0 < (ti j + r j) / 2 := by linarith [hti j, hr j]
      dsimp [d]
      split_ifs
      · exact div_pos hp hβpos
      · exact mul_pos hβpos hp
    have hb : ∀ j, threshold β s d i j = (ti j + r j) / 2 := by
      intro j
      unfold threshold
      dsimp [d]
      split_ifs <;> field_simp
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hne
    refine ⟨d, hd, ?_⟩
    rw [utility_sum, utility_sum]
    apply Finset.sum_lt_sum
    · intro j hj
      exact hpoint d i ti r j
    · refine ⟨j₀, Finset.mem_univ _, ?_⟩
      rcases lt_or_gt_of_ne hj₀ with hlt | hgt
      · have hr_own : bmwAlloc β s (Function.update d i r) j₀ = i := by
          by_contra h
          have hle := other_le β hβpos s d i r j₀ h
          rw [hb] at hle
          linarith
        have ht_other : bmwAlloc β s (Function.update d i ti) j₀ ≠ i := by
          intro h
          have hle := own_le β hβpos s d i ti j₀ h
          rw [hb] at hle
          linarith
        rw [if_pos hr_own, if_neg ht_other, hb]
        linarith
      · have ht_own : bmwAlloc β s (Function.update d i ti) j₀ = i := by
          by_contra h
          have hle := other_le β hβpos s d i ti j₀ h
          rw [hb] at hle
          linarith
        have hr_other : bmwAlloc β s (Function.update d i r) j₀ ≠ i := by
          intro h
          have hle := own_le β hβpos s d i r j₀ h
          rw [hb] at hle
          linarith
        rw [if_neg hr_other, if_pos ht_own, hb]
        linarith


theorem solution {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay := by
  constructor
  · intro s
    exact (bmw_strong (4 / 3) (by norm_num) s).1
  · intro i ti r hti hr hne
    let s : Fin k → Fin 2 := fun _ => 0
    obtain ⟨d, hd, hlt⟩ := (bmw_strong (4 / 3) (by norm_num) s).2 i ti r hti hr hne
    exact ⟨s, d, hd, hlt⟩
