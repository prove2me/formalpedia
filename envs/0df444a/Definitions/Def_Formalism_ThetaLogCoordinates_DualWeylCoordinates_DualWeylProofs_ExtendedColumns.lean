-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:00.707793+00:00
-- url     : https://prove2.me/theorems/ad051d6f-b47b-4437-bf0e-4582965b6f59
-- title:
--   Extended Columns
-- statement:
--   Definitions and structural lemmas for Extended Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ExtendedColumns.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT colHeight)
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch (TabP Dom cnt)
lemma qk_colH_low {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : c ≤ mu (lastIdx n)) :
    colH mu c = n := by
  unfold colH
  rw [filter_true_of_mem, card_univ, Fintype.card_fin]
  intro m _
  refine hc.trans (hmu ?_)
  show m.1 ≤ n - 1
  have := m.2
  omega
lemma qk_colH_high {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : mu 0 < c) :
    colH mu c = 0 := by
  unfold colH
  rw [filter_false_of_mem, card_empty]
  intro m _
  have : mu m ≤ mu 0 := hmu (Fin.zero_le m)
  omega
def extendedColumns {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ TCols mu then (I ⟨c, h⟩).1 else if c ≤ mu (lastIdx n) then univ else ∅
lemma qk_dom_univ {n : ℕ} (B : Finset (Fin n)) : Dom univ B := by
  intro x
  exact card_le_card (filter_subset_filter _ (subset_univ _))
lemma qk_dom_empty {n : ℕ} (A : Finset (Fin n)) : Dom A ∅ := by
  intro x
  simp [cnt]
lemma qk_dom_iff {n : ℕ} [NeZero n] (A B : Finset (Fin n)) :
    Dom A B ↔ ∀ t : Fin n, (B.filter (· ≤ t)).card ≤ (A.filter (· ≤ t)).card := by
  have key : ∀ (C : Finset (Fin n)) (t : Fin n), (C.filter (· ≤ t)).card = cnt C (t.1 + 1) := by
    intro C t
    unfold cnt
    congr 1
    ext a
    simp only [mem_filter, Fin.le_def, Nat.lt_succ_iff]
  constructor
  · intro h t
    rw [key, key]
    exact h _
  · intro h x
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [cnt]
    · by_cases hxn : x ≤ n
      · have := h ⟨x - 1, by omega⟩
        rw [key, key] at this
        have e : x - 1 + 1 = x := by omega
        simpa only [e] using this
      · have hn : 0 < n := NeZero.pos n
        have := h ⟨n - 1, by omega⟩
        rw [key, key] at this
        have e : n - 1 + 1 = n := by omega
        simp only [e] at this
        rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A (by omega), Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B (by omega),
          ← Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A le_rfl, ← Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B le_rfl]
        exact this
lemma qk_T_tab {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) (hI : StdT I) :
    TabP mu (extendedColumns I) := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · unfold extendedColumns
    split_ifs with h h2
    · exact (I ⟨c, h⟩).2
    · rw [card_univ, Fintype.card_fin]
      exact (qk_colH_low hmu h2).symm
    · rw [card_empty]
      refine (qk_colH_high hmu ?_).symm
      simp only [TCols, mem_Ioc, not_and, not_le] at h
      exact h (not_le.1 h2)
  · by_cases h1 : c ≤ mu (lastIdx n)
    · have : extendedColumns I c = univ := by
        unfold extendedColumns
        rw [dif_neg (by simp only [TCols, mem_Ioc]; omega), if_pos h1]
      rw [this]
      exact qk_dom_univ _
    · by_cases h2 : c + 1 ≤ mu 0
      · have hc : c ∈ TCols mu := by simp only [TCols, mem_Ioc]; omega
        have hc' : c + 1 ∈ TCols mu := by simp only [TCols, mem_Ioc]; omega
        have e1 : extendedColumns I c = (I ⟨c, hc⟩).1 := by unfold extendedColumns; rw [dif_pos hc]
        have e2 : extendedColumns I (c + 1) = (I ⟨c + 1, hc'⟩).1 := by unfold extendedColumns; rw [dif_pos hc']
        rw [e1, e2, qk_dom_iff]
        exact hI ⟨c, hc⟩ hc'
      · have : extendedColumns I (c + 1) = ∅ := by
          unfold extendedColumns
          rw [dif_neg (by simp only [TCols, mem_Ioc]; omega), if_neg (by omega)]
        rw [this]
        exact qk_dom_empty _
def qk_tabEquiv {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    {I : TIdx mu // StdT I} ≃ {T : ℤ → Finset (Fin n) // TabP mu T} where
  toFun I := ⟨extendedColumns I.1, qk_T_tab hmu I.1 I.2⟩
  invFun T := ⟨fun c => ⟨T.1 c, T.2.1 c⟩, fun c hc => (qk_dom_iff _ _).1 (T.2.2 c)⟩
  left_inv I := by
    apply Subtype.ext
    funext c
    apply Subtype.ext
    show extendedColumns I.1 c = _
    unfold extendedColumns
    rw [dif_pos c.2]
  right_inv T := by
    apply Subtype.ext
    funext c
    show extendedColumns _ c = _
    unfold extendedColumns
    split_ifs with h h2
    · rfl
    · symm
      rw [← card_eq_iff_eq_univ, Fintype.card_fin, T.2.1 c]
      exact qk_colH_low hmu h2
    · symm
      rw [← card_eq_zero, T.2.1 c]
      refine qk_colH_high hmu ?_
      simp only [TCols, mem_Ioc, not_and, not_le] at h
      exact h (not_le.1 h2)
end Formalism.InvariantFactorPaths.ColumnFamilies


