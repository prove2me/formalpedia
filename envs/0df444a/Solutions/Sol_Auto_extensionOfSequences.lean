-- Prove2me | solution 1 for Auto.extensionOfSequences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:50.770058+00:00
-- url     : https://prove2.me/submissions/6b8354a4-19f9-415c-a8fc-a28e5ee0305c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution (J : ℕ) (hJ : 0 < J) (a : ℤ → ℝ)
    (ha_pos : ∀ j : ℤ, 0 ≤ j → j < (J : ℤ) → 0 < a j)
    (ha_space : ∀ j : ℤ, 0 ≤ j → j + 1 < (J : ℤ) → 2 * a j ≤ a (j + 1)) :
    ∃! b : ℤ → ℝ, SpacedSequence b ∧
      (∀ j : ℤ, 0 ≤ j → j < (J : ℤ) → b j = a j) ∧
      (∀ j : ℤ, (J : ℤ) ≤ j → b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1)) ∧
      (∀ j : ℤ, j < 0 → b j = (2 : ℝ) ^ j * a 0) := by
  let b := aux_extensionOfSequence J a
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hfirst : 0 < a 0 := ha_pos 0 (by omega) (by omega)
  have hlast : 0 < a (J - 1) := by
    apply ha_pos (J - 1)
    · omega
    · omega
  have hb_pos : ∀ j : ℤ, 0 < b j := by
    intro j
    by_cases hneg : j < 0
    · rw [show b j = (2 : ℝ) ^ j * a 0 by simp [b, aux_extensionOfSequence, hneg]]
      exact mul_pos (zpow_pos (by norm_num) _) hfirst
    · by_cases hmid : j < (J : ℤ)
      · rw [show b j = a j by simp [b, aux_extensionOfSequence, hneg, hmid]]
        exact ha_pos j (le_of_not_gt hneg) hmid
      · rw [show b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1) by
          simp [b, aux_extensionOfSequence, hneg, hmid]]
        exact mul_pos (zpow_pos (by norm_num) _) hlast
  have hb_space : ∀ j : ℤ, 2 * b j ≤ b (j + 1) := by
    intro j
    by_cases hneg : j < 0
    · by_cases hmone : j = -1
      · subst j
        have hbneg : b (-1) = (2 : ℝ) ^ (-1 : ℤ) * a 0 := by
          simp [b, aux_extensionOfSequence]
        have hbzero : b 0 = a 0 := by
          simp [b, aux_extensionOfSequence, hJ]
        rw [hbneg]
        norm_num
        rw [hbzero]
        apply le_of_eq
        ring
      · have hneg' : j + 1 < 0 := by omega
        rw [show b j = (2 : ℝ) ^ j * a 0 by simp [b, aux_extensionOfSequence, hneg]]
        rw [show b (j + 1) = (2 : ℝ) ^ (j + 1) * a 0 by
          simp [b, aux_extensionOfSequence, hneg']]
        rw [zpow_add₀ htwo j 1]
        norm_num
        apply le_of_eq
        ring
    · have hj0 : 0 ≤ j := le_of_not_gt hneg
      by_cases hbefore : j + 1 < (J : ℤ)
      · have hj : j < (J : ℤ) := by omega
        have hnextneg : ¬ (j + 1 < 0) := by omega
        rw [show b j = a j by simp [b, aux_extensionOfSequence, hneg, hj],
          show b (j + 1) = a (j + 1) by
            simp [b, aux_extensionOfSequence, hnextneg, hbefore]]
        exact ha_space j hj0 hbefore
      · have hjge : (J : ℤ) ≤ j + 1 := le_of_not_gt hbefore
        by_cases hjlast : j = (J : ℤ) - 1
        · subst j
          have hJneg : ¬ ((J : ℤ) - 1 < 0) := by omega
          have hJlt : (J : ℤ) - 1 < (J : ℤ) := by omega
          rw [show b ((J : ℤ) - 1) = a ((J : ℤ) - 1) by
            simp [b, aux_extensionOfSequence, hJneg, hJlt]]
          rw [show b (((J : ℤ) - 1) + 1) = 2 * a ((J : ℤ) - 1) by
            rw [show ((J : ℤ) - 1) + 1 = J by omega]
            simp [b, aux_extensionOfSequence]]
        · have hjgeJ : (J : ℤ) ≤ j := by omega
          have hnextneg : ¬ (j + 1 < 0) := by omega
          have hjnotlt : ¬ (j < (J : ℤ)) := by omega
          have hnextnotlt : ¬ (j + 1 < (J : ℤ)) := by omega
          rw [show b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1) by
            simp [b, aux_extensionOfSequence, hneg, hjnotlt]]
          rw [show b (j + 1) = (2 : ℝ) ^ (j + 1 - J + 1) * a (J - 1) by
            simp [b, aux_extensionOfSequence, hnextneg, hnextnotlt]]
          rw [show j + 1 - J + 1 = (j - J + 1) + 1 by ring,
            zpow_add₀ htwo (j - J + 1) 1]
          norm_num
          apply le_of_eq
          ring
  refine ⟨b, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      exact ⟨hb_pos j, hb_space j⟩
    · intro j hj0 hjJ
      simp [b, aux_extensionOfSequence, not_lt.mpr hj0, hjJ]
    · intro j hj
      simp [b, aux_extensionOfSequence, not_lt.mpr (by omega : 0 ≤ j), not_lt.mpr hj]
    · intro j hj
      simp [b, aux_extensionOfSequence, hj]
  · intro c hc
    funext j
    by_cases hjneg : j < 0
    · rw [hc.2.2.2 j hjneg]
      simp [b, aux_extensionOfSequence, hjneg]
    · by_cases hjmid : j < (J : ℤ)
      · rw [hc.2.1 j (le_of_not_gt hjneg) hjmid]
        simp [b, aux_extensionOfSequence, hjneg, hjmid]
      · rw [hc.2.2.1 j (le_of_not_gt hjmid)]
        simp [b, aux_extensionOfSequence, hjneg, hjmid]
end Auto
