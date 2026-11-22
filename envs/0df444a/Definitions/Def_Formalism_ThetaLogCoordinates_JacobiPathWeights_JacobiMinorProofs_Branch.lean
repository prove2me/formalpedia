-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:38.887396+00:00
-- url     : https://prove2.me/theorems/ac463e74-9c21-441b-a080-7c7826b80198
-- title:
--   Branch
-- statement:
--   Definitions and structural lemmas for Branch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace Branch
def cnt {n : ℕ} (A : Finset (Fin n)) (x : ℕ) : ℕ := (A.filter fun a => a.val < x).card
theorem cnt_le_card {n : ℕ} (A : Finset (Fin n)) (x : ℕ) : cnt A x ≤ A.card := Finset.card_filter_le _ _
theorem cnt_of_le {n : ℕ} (A : Finset (Fin n)) {x : ℕ} (h : n ≤ x) : cnt A x = A.card := by
  unfold cnt
  congr 1
  exact Finset.filter_true_of_mem fun a _ => lt_of_lt_of_le a.isLt h
theorem nthElt_lt_iff {n : ℕ} (A : Finset (Fin n)) (a x : ℕ) (hx : x ≤ n) :
    nthElt A a < x ↔ a < cnt A x := by
  revert a
  refine Finset.induction_on_min A ?_ ?_
  · intro a
    have hnx : ¬ n < x := by omega
    simp [nthElt, cnt, hnx]
  · intro m s hm ih a
    have hms : m ∉ s := fun h => lt_irrefl m (hm m h)
    have hc : cnt (insert m s) x = cnt s x + if m.val < x then 1 else 0 := by
      unfold cnt
      rw [Finset.filter_insert]
      by_cases h : m.val < x
      · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (fun h' => hms (Finset.mem_filter.1 h').1)]
      · rw [if_neg h, if_neg h, Nat.add_zero]
    have hzero : ¬ m.val < x → cnt s x = 0 := by
      intro h
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy
      show ¬ y.val < x
      have hmy : m.val < y.val := hm y hy
      omega
    rw [hc]
    unfold nthElt at ih ⊢
    rw [Finset.sort_insert (· ≤ ·) (fun b hb => le_of_lt (hm b hb)) hms]
    rcases a with _ | k
    · rw [List.map_cons, List.getD_cons_zero]
      by_cases h : m.val < x
      · rw [if_pos h]
        constructor <;> intro <;> omega
      · rw [if_neg h, hzero h]
        constructor <;> intro <;> omega
    · rw [List.map_cons, List.getD_cons_succ, ih k]
      by_cases h : m.val < x
      · rw [if_pos h]
        constructor <;> intro <;> omega
      · rw [if_neg h, hzero h]
        constructor <;> intro <;> omega
def Dom {n : ℕ} (A B : Finset (Fin n)) : Prop := ∀ x, cnt B x ≤ cnt A x
theorem dom_iff {n : ℕ} (A B : Finset (Fin n)) :
    (∀ a < B.card, nthElt A a ≤ nthElt B a) ↔ Dom A B := by
  constructor
  · intro h
    have key : ∀ y ≤ n, cnt B y ≤ cnt A y := by
      intro y hy
      by_contra hlt
      push_neg at hlt
      have h1 : nthElt B (cnt A y) < y := (nthElt_lt_iff B (cnt A y) y hy).2 hlt
      have h2 : cnt A y < B.card := lt_of_lt_of_le hlt (cnt_le_card B y)
      have h4 : nthElt A (cnt A y) < y := lt_of_le_of_lt (h _ h2) h1
      exact lt_irrefl _ ((nthElt_lt_iff A (cnt A y) y hy).1 h4)
    intro x
    rcases le_total x n with hx | hx
    · exact key x hx
    · calc cnt B x = B.card := cnt_of_le B hx
        _ = cnt B n := (cnt_of_le B le_rfl).symm
        _ ≤ cnt A n := key n le_rfl
        _ = A.card := cnt_of_le A le_rfl
        _ = cnt A x := (cnt_of_le A hx).symm
  · intro hD a ha
    have hy : nthElt B a < n := (nthElt_lt_iff B a n le_rfl).2 (by rw [cnt_of_le B le_rfl]; exact ha)
    have h1 : a < cnt B (nthElt B a + 1) :=
      (nthElt_lt_iff B a (nthElt B a + 1) (by omega)).1 (Nat.lt_succ_self _)
    have h2 : a < cnt A (nthElt B a + 1) := lt_of_lt_of_le h1 (hD _)
    have h3 := (nthElt_lt_iff A a (nthElt B a + 1) (by omega)).2 h2
    omega
def TabP {n : ℕ} (μ : Fin n → ℤ) (T : ℤ → Finset (Fin n)) : Prop :=
  (∀ c, (T c).card = colHeight μ c) ∧ ∀ c, Dom (T c) (T (c + 1))
theorem hatIdx_hatIdx {n : ℕ} (I : ℤ → Finset (Fin n)) : hatIdx (hatIdx I) = I := by
  funext c
  by_cases h : (1 : ℤ) ≤ c <;> simp [hatIdx, h]
theorem isStd_iff {n : ℕ} (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : IsStd μ I ↔ TabP μ (hatIdx I) := by
  unfold IsStd IsIndex TabP
  apply and_congr
  · apply forall_congr'
    intro c
    have hI : (I c).card ≤ n := le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n)
    have hC : colHeight μ c ≤ n := le_of_le_of_eq (Finset.card_le_univ _) (Fintype.card_fin n)
    by_cases h : (1 : ℤ) ≤ c
    · simp only [hatIdx, h, ↓reduceIte]
    · simp only [hatIdx, h, ↓reduceIte, Finset.card_compl, Fintype.card_fin]
      omega
  · apply forall_congr'
    intro c
    exact dom_iff _ _
def stdEquiv {n : ℕ} (μ : Fin n → ℤ) :
    {I : ℤ → Finset (Fin n) // IsStd μ I} ≃ {T : ℤ → Finset (Fin n) // TabP μ T} :=
  Equiv.subtypeEquiv (Function.Involutive.toPerm hatIdx hatIdx_hatIdx) fun I => isStd_iff μ I
def restr {n : ℕ} (A : Finset (Fin (n + 1))) : Finset (Fin n) := univ.filter fun m => m.castSucc ∈ A
open Classical in

def extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) : Finset (Fin (n + 1)) :=
  A.map Fin.castSuccEmb ∪ if b then {Fin.last n} else ∅
theorem mem_restr {n : ℕ} (A : Finset (Fin (n + 1))) (m : Fin n) : m ∈ restr A ↔ m.castSucc ∈ A := by
  simp [restr]
theorem castSucc_mem_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) (m : Fin n) :
    m.castSucc ∈ extd A b ↔ m ∈ A := by
  have hne : m.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last m).ne
  unfold extd
  by_cases hb : b <;> simp [hb, hne]
theorem last_mem_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) : Fin.last n ∈ extd A b ↔ b := by
  have hne : ∀ a : Fin n, a.castSucc ≠ Fin.last n := fun a => (Fin.castSucc_lt_last a).ne
  unfold extd
  by_cases hb : b <;> simp [hb, hne]
theorem restr_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) : restr (extd A b) = A := by
  ext m
  rw [mem_restr, castSucc_mem_extd]
theorem extd_restr {n : ℕ} (A : Finset (Fin (n + 1))) (b : Prop) (h : b ↔ Fin.last n ∈ A) :
    extd (restr A) b = A := by
  ext x
  refine Fin.lastCases ?_ (fun m => ?_) x
  · rw [last_mem_extd]
    exact h
  · rw [castSucc_mem_extd, mem_restr]
theorem cnt_restr {n : ℕ} (A : Finset (Fin (n + 1))) {x : ℕ} (hx : x ≤ n) : cnt (restr A) x = cnt A x := by
  unfold cnt
  rw [← Finset.card_map Fin.castSuccEmb]
  congr 1
  ext a
  refine Fin.lastCases ?_ (fun m => ?_) a
  · have h1 : ¬ n < x := by omega
    have h2 : ∀ m : Fin n, m.castSucc ≠ Fin.last n := fun m => (Fin.castSucc_lt_last m).ne
    simp [h1, h2]
  · simp [mem_restr]
theorem card_extd_eq {n : ℕ} (A : Finset (Fin n)) (b : Prop) [Decidable b] :
    (extd A b).card = A.card + if b then 1 else 0 := by
  have hne : ∀ a : Fin n, a.castSucc ≠ Fin.last n := fun a => (Fin.castSucc_lt_last a).ne
  unfold extd
  by_cases hb : b
  · have hnm : Fin.last n ∉ A.map Fin.castSuccEmb := by simp [hne]
    rw [if_pos hb, if_pos hb, Finset.union_comm, ← Finset.insert_eq,
      Finset.card_insert_of_notMem hnm, Finset.card_map]
  · rw [if_neg hb, if_neg hb, Finset.union_empty, Finset.card_map, Nat.add_zero]
open Classical in
theorem card_eq_restr {n : ℕ} (A : Finset (Fin (n + 1))) :
    A.card = (restr A).card + if Fin.last n ∈ A then 1 else 0 := by
  have h := card_extd_eq (restr A) (Fin.last n ∈ A)
  rw [extd_restr A _ Iff.rfl] at h
  exact h
open Classical in
theorem card_extd {n : ℕ} (A : Finset (Fin n)) (b : Prop) :
    (extd A b).card = A.card + if b then 1 else 0 := by
  convert card_extd_eq A b
theorem colHeight_anti {n : ℕ} (μ : Fin n → ℤ) {c c' : ℤ} (h : c ≤ c') : colHeight μ c' ≤ colHeight μ c := by
  unfold colHeight
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  exact le_trans h hm
theorem mem_gtBox {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) :
    κ ∈ gtBox μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  unfold gtBox
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
theorem heights_of_gtBox {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ)
    (hκ : κ ∈ gtBox μ) (c : ℤ) : colHeight κ c ≤ colHeight μ c ∧ colHeight μ c ≤ colHeight κ c + 1 := by
  rw [mem_gtBox] at hκ
  constructor
  · unfold colHeight
    rw [← Finset.card_map Fin.castSuccEmb]
    apply Finset.card_le_card
    intro m hm
    rw [Finset.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi (hκ i).2
  · unfold colHeight
    have hsub : (univ.filter fun m => c ≤ μ m) ⊆
        insert 0 ((univ.filter fun i => c ≤ κ i).map (Fin.succEmb n)) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_insert, Finset.mem_map]
      rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨j, rfl⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨j, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_trans hm (hκ j).1
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (0 : Fin (n + 1)) ((univ.filter fun i => c ≤ κ i).map (Fin.succEmb n))
    rw [Finset.card_map] at h2
    omega
theorem tab_restr {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} {T : ℤ → Finset (Fin (n + 1))}
    (hT : TabP μ T) (hc : ∀ c, (restr (T c)).card = colHeight κ c) : TabP κ fun c => restr (T c) := by
  unfold TabP
  refine ⟨hc, fun c => ?_⟩
  intro x
  show cnt (restr (T (c + 1))) x ≤ cnt (restr (T c)) x
  rcases le_total x n with hx | hx
  · rw [cnt_restr _ hx, cnt_restr _ hx]
    exact hT.2 c x
  · rw [cnt_of_le _ hx, cnt_of_le _ hx, hc, hc]
    exact colHeight_anti κ (by omega)
theorem cnt_extd_eq_of_le {n : ℕ} (A : Finset (Fin n)) (b : Prop) {x : ℕ} (hx : x ≤ n) :
    cnt (extd A b) x = cnt A x := by
  rw [← cnt_restr _ hx, restr_extd]
theorem tab_extd {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ) (hκ : κ ∈ gtBox μ)
    {T' : ℤ → Finset (Fin n)} (hT : TabP κ T') :
    TabP μ fun c => extd (T' c) (colHeight κ c < colHeight μ c) := by
  have hcard : ∀ c, (extd (T' c) (colHeight κ c < colHeight μ c)).card = colHeight μ c := by
    intro c
    have h1 := card_extd (T' c) (colHeight κ c < colHeight μ c)
    have h2 := hT.1 c
    have h3 := heights_of_gtBox hμ hκ c
    rw [h1, h2]
    split_ifs <;> omega
  unfold TabP
  refine ⟨hcard, fun c => ?_⟩
  intro x
  show cnt (extd (T' (c + 1)) (colHeight κ (c + 1) < colHeight μ (c + 1))) x ≤
    cnt (extd (T' c) (colHeight κ c < colHeight μ c)) x
  by_cases hx : x ≤ n
  · rw [cnt_extd_eq_of_le _ _ hx, cnt_extd_eq_of_le _ _ hx]
    exact hT.2 c x
  · have hx' : n + 1 ≤ x := by omega
    rw [cnt_of_le _ hx', cnt_of_le _ hx', hcard, hcard]
    exact colHeight_anti μ (by omega)
def fibEquiv {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ) (hκ : κ ∈ gtBox μ) :
    {T : ℤ → Finset (Fin (n + 1)) // TabP μ T ∧ ∀ c, (restr (T c)).card = colHeight κ c} ≃
      {T' : ℤ → Finset (Fin n) // TabP κ T'} where
  toFun T := ⟨fun c => restr (T.1 c), tab_restr T.2.1 T.2.2⟩
  invFun T' := ⟨fun c => extd (T'.1 c) (colHeight κ c < colHeight μ c), tab_extd hμ hκ T'.2,
    fun c => by rw [restr_extd]; exact T'.2.1 c⟩
  left_inv T := by
    apply Subtype.ext
    funext c
    apply extd_restr
    have h1 := card_eq_restr (T.1 c)
    rw [T.2.1.1 c, T.2.2 c] at h1
    split_ifs at h1 with h
    · simp only [h, iff_true]; omega
    · simp only [h, iff_false]; omega
  right_inv T' := by
    apply Subtype.ext
    funext c
    exact restr_extd _ _
end Branch
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


