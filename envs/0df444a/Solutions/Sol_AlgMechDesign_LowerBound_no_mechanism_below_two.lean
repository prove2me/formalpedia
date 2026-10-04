-- Prove2me | solution 1 for AlgMechDesign.LowerBound.no_mechanism_below_two
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:14:03.485866+00:00
-- url     : https://prove2.me/submissions/8f844cf2-9faf-457a-86b0-21e6f8bbd661

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model
import Definitions.Def_AlgMechDesign_LowerBound_Mechanism



namespace AlgMechDesign.LowerBound

open Finset

theorem lbx_load_eq {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) :
    load t x i = ∑ j, if x j = i then t i j else 0 := by
  unfold load taskTime taskSet; rw [Finset.sum_filter]

theorem lbx_load_nonneg {n k : ℕ} {t : Fin n → Fin k → ℝ} (ht : IsType t) (x : Fin k → Fin n)
    (i : Fin n) : 0 ≤ load t x i := by
  rw [lbx_load_eq]
  exact Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact (ht i j).le; exact le_rfl])

theorem lbx_load_ge_two {n k : ℕ} {t : Fin n → Fin k → ℝ} (ht : IsType t) (x : Fin k → Fin n)
    (i : Fin n) (j1 j2 : Fin k) (hne : j1 ≠ j2) (h1 : x j1 = i) (h2 : x j2 = i) :
    t i j1 + t i j2 ≤ load t x i := by
  rw [lbx_load_eq]
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => if x j = i then t i j else 0)
    (Finset.subset_univ {j1, j2})
    (fun j _ _ => by split_ifs <;> [exact (ht i j).le; exact le_rfl])
  rw [Finset.sum_pair hne] at this
  simpa [h1, h2] using this

theorem lbx_load_ge_one {n k : ℕ} {t : Fin n → Fin k → ℝ} (ht : IsType t) (x : Fin k → Fin n)
    (i : Fin n) (j : Fin k) (h : x j = i) : t i j ≤ load t x i := by
  rw [lbx_load_eq]
  have := Finset.single_le_sum (f := fun j => if x j = i then t i j else 0)
    (fun j _ => by split_ifs <;> [exact (ht i j).le; exact le_rfl]) (Finset.mem_univ j)
  simpa [h] using this

theorem lbx_le_makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n)
    (i : Fin n) : load t x i ≤ makespan t x :=
  Finset.le_sup' (load t x) (Finset.mem_univ i)

theorem lbx_makespan_le {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n)
    (B : ℝ) (h : ∀ i, load t x i ≤ B) : makespan t x ≤ B :=
  Finset.sup'_le _ _ (fun i _ => h i)

theorem lbx_makespan_nonneg {n k : ℕ} [NeZero n] {t : Fin n → Fin k → ℝ} (ht : IsType t)
    (x : Fin k → Fin n) : 0 ≤ makespan t x :=
  (lbx_load_nonneg ht x 0).trans (lbx_le_makespan t x 0)

theorem lbx_load_le {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n)
    (S : Finset (Fin k)) (m : ℕ) (hS : S.card ≤ m) (w e : ℝ) (hw : 0 ≤ w) (he : 0 ≤ e)
    (h : ∀ j, x j = i → t i j ≤ (if j ∈ S then w else 0) + e) :
    load t x i ≤ m * w + k * e := by
  rw [lbx_load_eq]
  calc (∑ j, if x j = i then t i j else 0) ≤ ∑ j, ((if j ∈ S then w else 0) + e) :=
        Finset.sum_le_sum (fun j _ => by
          split_ifs with h1 h2 h2
          · simpa [h2] using h j h1
          · simpa [h2] using h j h1
          · linarith
          · linarith)
    _ = S.card * w + k * e := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]; simp
    _ ≤ m * w + k * e := by
        have : (S.card : ℝ) ≤ m := by exact_mod_cast hS
        nlinarith

theorem lbx_mono {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htruth : IsTruthful alloc pay)
    (d : Fin n → Fin k → ℝ) (hd : IsType d) (i : Fin n) (ti' : Fin k → ℝ)
    (hti' : IsAgentType ti') (hle : ∀ j, alloc d j = i → ti' j ≤ d i j)
    (hge : ∀ j, alloc d j ≠ i → d i j ≤ ti' j) (j : Fin k) :
    (alloc d j = i → ti' j < d i j → alloc (Function.update d i ti') j = i) ∧
    (alloc d j ≠ i → d i j < ti' j → alloc (Function.update d i ti') j ≠ i) := by
  have hdi : IsAgentType (d i) := fun j => hd i j
  have h1 := htruth d hd i (d i) ti' hdi hti'
  have h2 := htruth d hd i ti' (d i) hti' hdi
  rw [Function.update_eq_self] at h1 h2
  unfold utility at h1 h2
  set x := alloc d
  set x' := alloc (Function.update d i ti')
  have hT : ∀ f : Fin k → ℝ, ∀ y : Fin k → Fin n,
      taskTime f (taskSet y i) = ∑ j, if y j = i then f j else 0 := by
    intro f y; unfold taskTime taskSet; rw [Finset.sum_filter]
  rw [hT, hT] at h1 h2
  set E : Fin k → ℝ := fun j => ((if x j = i then ti' j else 0) - (if x j = i then d i j else 0))
    - ((if x' j = i then ti' j else 0) - (if x' j = i then d i j else 0)) with hE
  have hsum : 0 ≤ ∑ j, E j := by
    simp only [hE, Finset.sum_sub_distrib]; linarith
  have hneg : ∀ j ∈ (Finset.univ : Finset (Fin k)), E j ≤ 0 := by
    intro j _
    simp only [hE]
    by_cases ha : x j = i <;> by_cases hb : x' j = i <;> simp only [ha, hb, if_true, if_false]
    · linarith
    · linarith [hle j ha]
    · linarith [hge j ha]
    · linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos hneg).1 (le_antisymm (Finset.sum_nonpos hneg) hsum)
  have hj := hzero j (Finset.mem_univ j)
  simp only [hE] at hj
  constructor
  · intro ha hlt
    by_contra hb
    simp only [ha, hb, if_true, if_false] at hj
    linarith
  · intro ha hlt hb
    simp only [ha, hb, if_true, if_false] at hj
    linarith


theorem lbx_caseA {n k : ℕ} [NeZero n] {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htruth : IsTruthful alloc pay) {C : ℝ}
    (hC0 : 0 ≤ C) (hC2 : C < 2) (happ : IsApprox C alloc) {ε : ℝ} (hε0 : 0 < ε)
    (hε : 10 * ((k : ℝ) + 1) * ε = 2 - C) (T : Fin n → Fin k → ℝ)
    (hTdef : ∀ i j, T i j = if i.val < 2 then (if j.val < 3 then 1 else ε) else 4)
    (a b : Fin n) (ha : a.val < 2) (hb : b.val < 2) (hab : a ≠ b)
    (q0 q1 q2 : Fin k) (hq0 : q0.val = 0) (hq1 : q1.val = 1) (hq2 : q2.val = 2)
    (h0 : alloc T q0 = a) (h1 : alloc T q1 = a) (h2 : alloc T q2 = a) : False := by
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hε1 : ε < 1 / 2 := by nlinarith
  have hT : IsType T := by intro i j; rw [hTdef]; split_ifs <;> linarith
  have hTa : ∀ j : Fin k, T a j = if j.val < 3 then 1 else ε := by
    intro j; rw [hTdef, if_pos ha]
  have hTb : ∀ j : Fin k, T b j = if j.val < 3 then 1 else ε := by
    intro j; rw [hTdef, if_pos hb]
  have h02 : q0 ≠ q2 := by intro h; rw [Fin.ext_iff] at h; omega
  have h12 : q1 ≠ q2 := by intro h; rw [Fin.ext_iff] at h; omega
  have h01 : q0 ≠ q1 := by intro h; rw [Fin.ext_iff] at h; omega
  set t' : Fin k → ℝ := fun j => if alloc T j = a then (if j = q2 then ε else T a j * (1 - ε))
    else T a j with ht'
  have ht'pos : IsAgentType t' := by
    intro j; simp only [ht']
    have := hT a j
    split_ifs
    · exact hε0
    · nlinarith
    · exact this
  have hmono := lbx_mono htruth T hT a t' ht'pos
    (by intro j hj; simp only [ht', if_pos hj]; rw [hTa]; split_ifs <;> nlinarith)
    (by intro j hj; simp only [ht', if_neg hj]; exact le_rfl)
  have hx0 : alloc (Function.update T a t') q0 = a :=
    (hmono q0).1 h0 (by simp only [ht', if_pos h0, if_neg h02]; rw [hTa, if_pos (by omega)]; linarith)
  have hx1 : alloc (Function.update T a t') q1 = a :=
    (hmono q1).1 h1 (by simp only [ht', if_pos h1, if_neg h12]; rw [hTa, if_pos (by omega)]; linarith)
  have ht2 : IsType (Function.update T a t') := by
    intro i j
    by_cases hia : i = a
    · subst hia; simp only [Function.update_self]; exact ht'pos j
    · rw [Function.update_of_ne hia]; exact hT i j
  have hload := lbx_load_ge_two ht2 _ a q0 q1 h01 hx0 hx1
  simp only [Function.update_self, ht', if_pos h0, if_pos h1, if_neg h02, if_neg h12] at hload
  rw [hTa, hTa, if_pos (by omega), if_pos (by omega)] at hload
  have hy : makespan (Function.update T a t') (fun j => if j = q1 then b else a) ≤ 1 * 1 + k * ε := by
    apply lbx_makespan_le; intro i
    by_cases hia : i = a
    · subst hia
      refine le_trans (lbx_load_le _ _ _ {q0} 1 (by simp) 1 ε (by norm_num) hε0.le ?_) (by push_cast; nlinarith)
      intro j hj
      simp only [Function.update_self, ht', Finset.mem_singleton]
      rw [hTa]
      by_cases hj1 : j = q1
      · rw [if_pos hj1] at hj; exact absurd hj.symm hab
      by_cases hj0 : j = q0
      · subst hj0; rw [if_pos h0, if_neg h02, if_pos (by omega), if_pos rfl]; nlinarith
      by_cases hj2 : j = q2
      · subst hj2; rw [if_pos h2, if_pos rfl, if_neg h02.symm]; linarith
      have hj3 : ¬ j.val < 3 := by
        simp only [Fin.ext_iff] at hj0 hj1 hj2; omega
      rw [if_neg hj0, if_neg hj3]
      split_ifs <;> nlinarith
    by_cases hib : i = b
    · subst hib
      refine le_trans (lbx_load_le _ _ _ {q1} 1 (by simp) 1 ε (by norm_num) hε0.le ?_) (by push_cast; nlinarith)
      intro j hj
      rw [Function.update_of_ne hia, hTb]
      by_cases hj1 : j = q1
      · subst hj1; rw [if_pos (by omega), if_pos (Finset.mem_singleton_self _)]; linarith
      · rw [if_neg hj1] at hj; exact absurd hj.symm hia
    · refine le_trans (lbx_load_le _ _ _ ∅ 0 (by simp) 1 ε (by norm_num) hε0.le ?_) (by push_cast; nlinarith)
      intro j hj
      exfalso
      split_ifs at hj with hj1
      · exact hib hj.symm
      · exact hia hj.symm
  have happ1 := happ _ ht2 (fun j => if j = q1 then b else a)
  have hl := lbx_le_makespan (Function.update T a t') (alloc (Function.update T a t')) a
  have hCy : C * makespan (Function.update T a t') (fun j => if j = q1 then b else a)
      ≤ C * (1 * 1 + k * ε) := mul_le_mul_of_nonneg_left hy hC0
  have hkε : 0 ≤ (k:ℝ) * ε := by positivity
  nlinarith

theorem lbx_caseB {n k : ℕ} [NeZero n] {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htruth : IsTruthful alloc pay) {C : ℝ}
    (hC0 : 0 ≤ C) (hC2 : C < 2) (happ : IsApprox C alloc) {ε : ℝ} (hε0 : 0 < ε)
    (hε : 10 * ((k : ℝ) + 1) * ε = 2 - C) (T : Fin n → Fin k → ℝ)
    (hTdef : ∀ i j, T i j = if i.val < 2 then (if j.val < 3 then 1 else ε) else 4)
    (a b : Fin n) (ha : a.val < 2) (hb : b.val < 2) (hab : a ≠ b)
    (j1 j2 j3 : Fin k) (hj1 : j1.val < 3) (hj2 : j2.val < 3) (hj3 : j3.val < 3)
    (h12 : j1 ≠ j2) (h13 : j1 ≠ j3) (h23 : j2 ≠ j3)
    (h1 : alloc T j1 = a) (h2 : alloc T j2 = a) (h3 : alloc T j3 = b) : False := by
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hε1 : ε < 1 / 2 := by nlinarith
  have hT : IsType T := by intro i j; rw [hTdef]; split_ifs <;> linarith
  have hTa : ∀ j : Fin k, T a j = if j.val < 3 then 1 else ε := by
    intro j; rw [hTdef, if_pos ha]
  have hTb : ∀ j : Fin k, T b j = if j.val < 3 then 1 else ε := by
    intro j; rw [hTdef, if_pos hb]
  have hmain : ∀ i : Fin n, i.val < 2 → i = a ∨ i = b := by
    intro i hi
    simp only [Fin.ext_iff] at hab ⊢; omega
  have hthree : ∀ j : Fin k, j.val < 3 → j = j1 ∨ j = j2 ∨ j = j3 := by
    intro j hj
    simp only [Fin.ext_iff] at h12 h13 h23 ⊢; omega
  set t' : Fin k → ℝ := fun j => if alloc T j = b then (if j = j3 then ε else T b j / 2)
    else T b j * (1 + ε) with ht'
  have ht'pos : IsAgentType t' := by
    intro j; simp only [ht']
    have := hT b j
    split_ifs
    · exact hε0
    · linarith
    · nlinarith
  have hmono := lbx_mono htruth T hT b t' ht'pos
    (by intro j hj; simp only [ht', if_pos hj]; rw [hTb]; split_ifs <;> nlinarith)
    (by intro j hj; simp only [ht', if_neg hj]; have := hT b j; nlinarith)
  have hstay : ∀ j, alloc T j ≠ b → alloc (Function.update T b t') j ≠ b := by
    intro j hj
    exact (hmono j).2 hj (by simp only [ht', if_neg hj]; have := hT b j; nlinarith)
  have ht2 : IsType (Function.update T b t') := by
    intro i j
    by_cases hia : i = b
    · subst hia; simp only [Function.update_self]; exact ht'pos j
    · rw [Function.update_of_ne hia]; exact hT i j
  set y : Fin k → Fin n := fun j => if j = j1 then a else b with hydef
  have hy : makespan (Function.update T b t') y ≤ 1 * (1 + ε) + k * (2 * ε) := by
    apply lbx_makespan_le; intro i
    by_cases hia : i = a
    · subst hia
      refine le_trans (lbx_load_le _ _ _ {j1} 1 (by simp) (1 + ε) (2 * ε) (by linarith) (by linarith) ?_) (by push_cast; nlinarith)
      intro j hj
      rw [Function.update_of_ne hab, hTa]
      by_cases hjj : j = j1
      · subst hjj; simp [hj1]; linarith
      · simp only [hydef, if_neg hjj] at hj; exact absurd hj.symm hab
    by_cases hib : i = b
    · subst hib
      refine le_trans (lbx_load_le _ _ _ {j2} 1 (by simp) (1 + ε) (2 * ε) (by linarith) (by linarith) ?_) (by push_cast; nlinarith)
      intro j hj
      simp only [Function.update_self, ht', Finset.mem_singleton]
      rw [hTb]
      have hjj1 : j ≠ j1 := by
        intro h; subst h; simp only [hydef, if_pos rfl] at hj; exact hab hj
      by_cases hjj2 : j = j2
      · subst hjj2; rw [if_neg (by rw [h2]; exact hab), if_pos hj2, if_pos rfl]; linarith
      by_cases hjj3 : j = j3
      · subst hjj3; rw [if_pos h3, if_pos rfl, if_neg (Ne.symm h23)]; linarith
      have hj3' : ¬ j.val < 3 := by
        intro h; rcases hthree j h with h | h | h <;> contradiction
      rw [if_neg hjj2, if_neg hjj3, if_neg hj3']
      split_ifs <;> nlinarith
    · refine le_trans (lbx_load_le _ _ _ ∅ 0 (by simp) (1 + ε) (2 * ε) (by linarith) (by linarith) ?_) (by push_cast; nlinarith)
      intro j hj
      exfalso
      simp only [hydef] at hj
      split_ifs at hj with hjj
      · exact hia hj.symm
      · exact hib hj.symm
  have happ1 := happ _ ht2 y
  have hCy : C * makespan (Function.update T b t') y ≤ C * (1 * (1 + ε) + k * (2 * ε)) :=
    mul_le_mul_of_nonneg_left hy hC0
  have hkε : 0 ≤ (k:ℝ) * ε := by positivity
  have hm4 : makespan (Function.update T b t') (alloc (Function.update T b t')) < 4 := by
    nlinarith
  have hgo : ∀ j, alloc T j = a → alloc (Function.update T b t') j = a := by
    intro j hj
    have hnb := hstay j (by rw [hj]; exact hab)
    have hlt : (alloc (Function.update T b t') j).val < 2 := by
      by_contra hcon
      have := lbx_load_ge_one ht2 (alloc (Function.update T b t')) (alloc (Function.update T b t') j) j rfl
      rw [Function.update_of_ne hnb, hTdef, if_neg hcon] at this
      linarith [lbx_le_makespan (Function.update T b t') (alloc (Function.update T b t'))
        (alloc (Function.update T b t') j)]
    rcases hmain _ hlt with h | h
    · exact h
    · exact absurd h hnb
  have hload := lbx_load_ge_two ht2 _ a j1 j2 h12 (hgo j1 h1) (hgo j2 h2)
  rw [Function.update_of_ne hab, hTa, hTa, if_pos hj1, if_pos hj2] at hload
  have hl := lbx_le_makespan (Function.update T b t') (alloc (Function.update T b t')) a
  nlinarith


theorem lbx_core {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k)
    {c : ℝ} (hc : c < 2) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay) :
    ¬ IsApprox c alloc := by
  intro happ0
  obtain ⟨C, hC0, hC2, happ⟩ : ∃ C : ℝ, 0 ≤ C ∧ C < 2 ∧ IsApprox C alloc :=
    ⟨max c 0, le_max_right _ _, max_lt hc (by norm_num), fun t ht y =>
      (happ0 t ht y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (lbx_makespan_nonneg ht y))⟩
  obtain ⟨ε, hε0, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ 10 * ((k : ℝ) + 1) * ε = 2 - C :=
    ⟨(2 - C) / (10 * ((k : ℝ) + 1)), div_pos (by linarith) (by positivity),
      by field_simp⟩
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hkε : 0 ≤ (k:ℝ) * ε := by positivity
  obtain ⟨T, hTdef⟩ : ∃ T : Fin n → Fin k → ℝ,
      ∀ i j, T i j = if i.val < 2 then (if j.val < 3 then 1 else ε) else 4 :=
    ⟨fun i j => if i.val < 2 then (if j.val < 3 then 1 else ε) else 4, fun _ _ => rfl⟩
  have hT : IsType T := by intro i j; rw [hTdef]; split_ifs <;> linarith
  obtain ⟨p0, hp0⟩ : ∃ p : Fin n, p.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ p : Fin n, p.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q : Fin k, q.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ q : Fin k, q.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q : Fin k, q.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have hp01 : p0 ≠ p1 := by intro h; rw [Fin.ext_iff] at h; omega
  have h01 : q0 ≠ q1 := by intro h; rw [Fin.ext_iff] at h; omega
  have h02 : q0 ≠ q2 := by intro h; rw [Fin.ext_iff] at h; omega
  have h12 : q1 ≠ q2 := by intro h; rw [Fin.ext_iff] at h; omega
  have hy : makespan T (fun j => if j = q2 then p1 else p0) ≤ 1 * 2 + k * ε := by
    apply lbx_makespan_le; intro i
    by_cases hi : i = p1
    · subst hi
      refine le_trans (lbx_load_le _ _ _ {q2} 2 (by simp) 1 ε (by norm_num)
        hε0.le ?_) (by push_cast; nlinarith)
      intro j hj
      rw [hTdef]
      by_cases hj2 : j = q2
      · subst hj2
        rw [if_pos (by omega), if_pos (by omega), if_pos (Finset.mem_singleton_self _)]; linarith
      · rw [if_neg hj2] at hj; exact absurd hj hp01
    · refine le_trans (lbx_load_le _ _ _ {q0, q1} 2 (Finset.card_le_two) 1 ε (by norm_num)
        hε0.le ?_) (by push_cast; nlinarith)
      intro j hj
      rw [hTdef]
      by_cases hj2 : j = q2
      · rw [if_pos hj2] at hj; exact absurd hj.symm hi
      · rw [if_neg hj2] at hj; subst hj
        rw [if_pos (by omega)]
        by_cases hj3 : j.val < 3
        · have : j ∈ ({q0, q1} : Finset (Fin k)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hj2 ⊢; omega
          rw [if_pos hj3, if_pos this]; linarith
        · rw [if_neg hj3]; split_ifs <;> linarith
  have hb := happ T hT (fun j => if j = q2 then p1 else p0)
  have hm4 : makespan T (alloc T) < 4 := by
    have := mul_le_mul_of_nonneg_left hy hC0
    nlinarith
  have hmain : ∀ j, alloc T j = p0 ∨ alloc T j = p1 := by
    intro j
    have hlt : (alloc T j).val < 2 := by
      by_contra hcon
      have := lbx_load_ge_one hT (alloc T) (alloc T j) j rfl
      rw [hTdef, if_neg hcon] at this
      linarith [lbx_le_makespan T (alloc T) (alloc T j)]
    simp only [Fin.ext_iff]; omega
  have hp0l : p0.val < 2 := by omega
  have hp1l : p1.val < 2 := by omega
  have hA := @lbx_caseA n k _ alloc pay htruth C hC0 hC2 happ ε hε0 hε T hTdef
  have hB := @lbx_caseB n k _ alloc pay htruth C hC0 hC2 happ ε hε0 hε T hTdef
  have hv0 : q0.val < 3 := by omega
  have hv1 : q1.val < 3 := by omega
  have hv2 : q2.val < 3 := by omega
  rcases hmain q0 with a0 | a0 <;> rcases hmain q1 with a1 | a1 <;>
    rcases hmain q2 with a2 | a2
  · exact hA p0 p1 hp0l hp1l hp01 q0 q1 q2 hq0 hq1 hq2 a0 a1 a2
  · exact hB p0 p1 hp0l hp1l hp01 q0 q1 q2 hv0 hv1 hv2 h01 h02 h12 a0 a1 a2
  · exact hB p0 p1 hp0l hp1l hp01 q0 q2 q1 hv0 hv2 hv1 h02 h01 h12.symm a0 a2 a1
  · exact hB p1 p0 hp1l hp0l hp01.symm q1 q2 q0 hv1 hv2 hv0 h12 h01.symm h02.symm a1 a2 a0
  · exact hB p0 p1 hp0l hp1l hp01 q1 q2 q0 hv1 hv2 hv0 h12 h01.symm h02.symm a1 a2 a0
  · exact hB p1 p0 hp1l hp0l hp01.symm q0 q2 q1 hv0 hv2 hv1 h02 h01 h12.symm a0 a2 a1
  · exact hB p1 p0 hp1l hp0l hp01.symm q0 q1 q2 hv0 hv1 hv2 h01 h02 h12 a0 a1 a2
  · exact hA p1 p0 hp1l hp0l hp01.symm q0 q1 q2 hq0 hq1 hq2 a0 a1 a2


universe u

theorem lbx_goal_core {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k) {c : ℝ}
    (hc : c < 2) {A : Fin n → Type u} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) :
    ¬ Implements o p c := by
  rintro ⟨hdom, happ⟩
  classical
  let s : (i : Fin n) → (Fin k → ℝ) → A i := fun i ti =>
    if h : IsAgentType ti then Classical.choose (hdom i ti h)
    else Classical.choose (hdom i (fun _ => 1) (fun _ => one_pos))
  have hs : ∀ i ti, IsAgentType ti → IsDominant o p i ti (s i ti) := by
    intro i ti h; simp only [s, dif_pos h]; exact Classical.choose_spec (hdom i ti h)
  have hupd : ∀ (d : Fin n → Fin k → ℝ) (i : Fin n) (ti : Fin k → ℝ),
      (fun j => s j (Function.update d i ti j)) = Function.update (fun j => s j (d j)) i (s i ti) := by
    intro d i ti; funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  refine lbx_core hn hk hc (fun d => o (fun i => s i (d i))) (fun d => p (fun i => s i (d i))) ?_ ?_
  · intro d hd i ti ti' hti hti'
    have := hs i ti hti (fun j => s j (d j)) (s i ti')
    unfold genUtility at this
    unfold utility
    simp only [hupd]
    exact this
  · intro t ht y
    exact happ t ht _ (fun i => hs i (t i) (fun j => ht i j)) y

end AlgMechDesign.LowerBound

open AlgMechDesign.LowerBound
universe u

theorem solution {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k) {c : ℝ}
    (hc : c < 2) {A : Fin n → Type u} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) :
    ¬ Implements o p c := by
  exact lbx_goal_core hn hk hc o p
