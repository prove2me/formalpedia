-- Prove2me | solution 1 for Arxiv0812_1178.closure_kernel_eq_baseline_range
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:20:08.902823+00:00
-- url     : https://prove2.me/submissions/ec7dcd7c-883d-4c85-bc86-b4e0becf03ec

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178

private lemma baselineOp_mulVec (n : ℕ) (v : Fin n → ℝ) (b : Baseline n) :
    (baselineOp n *ᵥ v) b = v b.1.2 - v b.1.1 := by
  simp [baselineOp, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

private lemma closureOp_mulVec {n : ℕ} (hn : 1 ≤ n) (φ : Baseline n → ℝ) (c : ClosureIdx n) :
    (closureOp n *ᵥ φ) c =
      φ ⟨(⟨0, by omega⟩, c.1.1), c.2.1⟩ +
      φ ⟨c.1, c.2.2⟩ -
      φ ⟨(⟨0, by omega⟩, c.1.2), lt_trans c.2.1 c.2.2⟩ := by
  let b1 : Baseline n := ⟨(⟨0, by omega⟩, c.1.1), c.2.1⟩
  let b2 : Baseline n := ⟨c.1, c.2.2⟩
  let b3 : Baseline n := ⟨(⟨0, by omega⟩, c.1.2), lt_trans c.2.1 c.2.2⟩
  have h1 : ∀ b : Baseline n, (b.1.1.1 = 0 ∧ b.1.2 = c.1.1) ↔ b = b1 := by
    intro b
    constructor
    · rintro ⟨h0, h2⟩
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext h0
      · exact h2
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have h2 : ∀ b : Baseline n, b.1 = c.1 ↔ b = b2 := by
    intro b
    constructor
    · intro h; exact Subtype.ext h
    · rintro rfl; rfl
  have h3 : ∀ b : Baseline n, (b.1.1.1 = 0 ∧ b.1.2 = c.1.2) ↔ b = b3 := by
    intro b
    constructor
    · rintro ⟨h0, h2⟩
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext h0
      · exact h2
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [closureOp, Matrix.mulVec, dotProduct, h1, h2, h3, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

private lemma closureOp_mul_baselineOp {n : ℕ} (hn : 3 ≤ n) :
    closureOp n * baselineOp n = 0 := by
  ext c j
  have h0 : ((closureOp n * baselineOp n) *ᵥ Pi.single j (1 : ℝ)) c = 0 := by
    rw [← Matrix.mulVec_mulVec, closureOp_mulVec (by omega)]
    simp only [baselineOp_mulVec]
    ring
  simpa [Matrix.mulVec_single_one] using h0

private lemma ker_closureOp_eq_range_baselineOp {n : ℕ} (hn : 3 ≤ n) :
    LinearMap.ker (closureOp n).mulVecLin = LinearMap.range (baselineOp n).mulVecLin := by
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · intro hφ
    refine ⟨fun j => if hj : 0 < j.1 then φ ⟨(⟨0, by omega⟩, j), hj⟩ else 0, ?_⟩
    ext b
    rw [baselineOp_mulVec]
    have hb2 : 0 < b.1.2.1 := lt_of_le_of_lt (Nat.zero_le _) b.2
    by_cases hb1 : 0 < b.1.1.1
    · simp only [dif_pos hb2, dif_pos hb1]
      let c : ClosureIdx n := ⟨b.1, ⟨hb1, b.2⟩⟩
      have hc := congr_fun hφ c
      rw [closureOp_mulVec (by omega)] at hc
      have hb_eq : (⟨c.1, c.2.2⟩ : Baseline n) = b := Subtype.ext rfl
      rw [hb_eq] at hc
      simp only [c, Pi.zero_apply] at hc
      linarith
    · have hb1_zero : b.1.1 = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
      simp only [dif_pos hb2, dif_neg hb1, sub_zero]
      congr 1
      exact Subtype.ext (Prod.ext hb1_zero.symm rfl)
  · rintro ⟨v, rfl⟩
    rw [Matrix.mulVec_mulVec, closureOp_mul_baselineOp hn, Matrix.zero_mulVec]

private lemma finrank_ker_baselineOp {n : ℕ} (hn : 3 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (baselineOp n).mulVecLin) = 1 := by
  let ones : Fin n → ℝ := fun _ => 1
  have hker : LinearMap.ker (baselineOp n).mulVecLin = Submodule.span ℝ {ones} := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro hv
      refine ⟨v ⟨0, by omega⟩, ?_⟩
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, ones, mul_one]
      by_cases hj : 0 < j.1
      · let b : Baseline n := ⟨(⟨0, by omega⟩, j), hj⟩
        have hb := congr_fun hv b
        rw [baselineOp_mulVec] at hb
        simp only [b, Pi.zero_apply] at hb
        linarith
      · have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
        rw [hj0]
    · rintro ⟨a, rfl⟩
      ext b
      rw [baselineOp_mulVec]
      simp [ones]
  rw [hker]
  have hne : ones ≠ 0 := by
    intro h
    have := congr_fun h ⟨0, by omega⟩
    simp [ones] at this
  exact finrank_span_singleton hne

private lemma rank_baselineOp {n : ℕ} (hn : 3 ≤ n) :
    (baselineOp n).rank = n - 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (baselineOp n).mulVecLin
  rw [finrank_ker_baselineOp hn, Module.finrank_pi, Fintype.card_fin] at hrn
  have hr : (baselineOp n).rank = Module.finrank ℝ (LinearMap.range (baselineOp n).mulVecLin) := rfl
  omega

private lemma card_baseline (n : ℕ) :
    Fintype.card (Baseline n) = n * (n - 1) / 2 := by
  have h2 : 2 * Fintype.card (Baseline n) + n = n * n := by
    let Slt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)
    let Sgt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.2 < p.1)
    let Seq : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 = p.2)
    have hcard_lt : Fintype.card (Baseline n) = Slt.card := by
      rw [Fintype.card_subtype]
    have hswap : Slt.card = Sgt.card := by
      refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
      · intro p hp
        simp only [Slt, Sgt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro p1 _ p2 _ h
        exact Prod.swap_injective h
      · intro p hp
        refine ⟨p.swap, ?_, Prod.swap_swap p⟩
        simp only [Slt, Sgt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
    have heq : Seq.card = n := by
      have : Seq.card = (Finset.univ : Finset (Fin n)).card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 h
          simp only [Seq, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          exact Prod.ext h (hp1.symm.trans (h.trans hp2))
        · intro i _
          exact ⟨(i, i), by simp [Seq], rfl⟩
      rw [this, Finset.card_fin]
    have hunion : Slt ∪ Seq ∪ Sgt = Finset.univ := by
      ext p
      simp only [Slt, Seq, Sgt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hd1 : Disjoint Slt Seq := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Slt, Seq, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      exact ne_of_lt hp1 hp2
    have hd2 : Disjoint (Slt ∪ Seq) Sgt := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Slt, Seq, Sgt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      rcases hp1 with h | h
      · exact lt_asymm h hp2
      · exact ne_of_gt hp2 h
    have htot := congr_arg Finset.card hunion
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at htot
    omega
  have hmul : n * n = n * (n - 1) + n := by
    cases n with
    | zero => simp
    | succ k => simp [Nat.mul_succ, Nat.succ_mul]
  have h2eq : 2 * Fintype.card (Baseline n) = n * (n - 1) := by omega
  omega

private lemma card_closureIdx {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card (ClosureIdx n) = (n - 1) * (n - 2) / 2 := by
  let e : ClosureIdx n ≃ Baseline (n - 1) :=
    { toFun := fun c =>
        ⟨(⟨c.1.1.1 - 1, by have := c.1.1.2; have := c.2.1; omega⟩,
          ⟨c.1.2.1 - 1, by have := c.1.2.2; have := c.2.1; have := c.2.2; omega⟩),
          by show c.1.1.1 - 1 < c.1.2.1 - 1; have := c.2.1; have := c.2.2; omega⟩
      invFun := fun b =>
        ⟨(⟨b.1.1.1 + 1, by have := b.1.1.2; omega⟩,
          ⟨b.1.2.1 + 1, by have := b.1.2.2; omega⟩),
          ⟨by simp, by show b.1.1.1 + 1 < b.1.2.1 + 1; exact Nat.add_lt_add_right b.2 1⟩⟩
      left_inv := fun c => by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp only
        · have := c.2.1; omega
        · have := c.2.1; have := c.2.2; omega
      right_inv := fun b => by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> simp }
  rw [Fintype.card_congr e, card_baseline (n - 1)]
  have : n - 1 - 1 = n - 2 := by omega
  rw [this]

private lemma finrank_ker_closureOp {n : ℕ} (hn : 3 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) = n - 1 := by
  rw [ker_closureOp_eq_range_baselineOp hn]
  exact rank_baselineOp hn

theorem solution {n : ℕ} (hn : 3 ≤ n) :
    closureOp n * baselineOp n = 0 ∧
    (baselineOp n).rank = n - 1 ∧
    Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) ≤ n - 1 ∧
    LinearMap.ker (closureOp n).mulVecLin = LinearMap.range (baselineOp n).mulVecLin ∧
    Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) = n - 1 ∧
    Fintype.card (Baseline n) = n * (n - 1) / 2 ∧
    Fintype.card (ClosureIdx n) = (n - 1) * (n - 2) / 2 ∧
    (closureOp n).rank = (n - 1) * (n - 2) / 2 ∧
    (∀ m : ℕ, n < m →
      (Module.finrank ℝ (LinearMap.ker (closureOp m).mulVecLin) : ℝ) / Fintype.card (Baseline m) <
        (Module.finrank ℝ (LinearMap.ker (closureOp n).mulVecLin) : ℝ) /
          Fintype.card (Baseline n)) := by
  have hCB := closureOp_mul_baselineOp hn
  have hrankB := rank_baselineOp hn
  have hker_eq := ker_closureOp_eq_range_baselineOp hn
  have hker_fr := finrank_ker_closureOp hn
  have hcardB := card_baseline n
  have hcardC := card_closureIdx (by omega : 1 ≤ n)
  have hrankC : (closureOp n).rank = (n - 1) * (n - 2) / 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (closureOp n).mulVecLin
    rw [hker_fr, Module.finrank_pi, hcardB] at hrn
    have hr : (closureOp n).rank = Module.finrank ℝ (LinearMap.range (closureOp n).mulVecLin) := rfl
    have heven1 : 2 ∣ n * (n - 1) := by
      cases n with
      | zero => simp
      | succ k =>
        simpa [Nat.succ_sub_one, mul_comm] using Nat.even_mul_succ_self k |>.two_dvd
    have heven2 : 2 ∣ (n - 1) * (n - 2) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have : (k + 2 - 1) * (k + 2 - 2) = k * (k + 1) := by
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h2 : k + 2 - 2 = k := by omega
        rw [h1, h2, mul_comm]
      rw [this]
      exact (Nat.even_mul_succ_self k).two_dvd
    have hdiv1 : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' heven1
    have hdiv2 : 2 * ((n - 1) * (n - 2) / 2) = (n - 1) * (n - 2) := Nat.mul_div_cancel' heven2
    have hident : n * (n - 1) = (n - 1) * (n - 2) + 2 * (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have h1 : k + 2 - 1 = k + 1 := by omega
      have h2 : k + 2 - 2 = k := by omega
      rw [h1, h2]
      ring
    omega
  refine ⟨hCB, hrankB, le_of_eq hker_fr, hker_eq, hker_fr, hcardB, hcardC, hrankC, ?_⟩
  intro m hm
  have hm3 : 3 ≤ m := by omega
  have hratio : ∀ k : ℕ, 3 ≤ k →
      (Module.finrank ℝ (LinearMap.ker (closureOp k).mulVecLin) : ℝ) / Fintype.card (Baseline k) =
        2 / (k : ℝ) := by
    intro k hk
    rw [finrank_ker_closureOp hk, card_baseline k]
    have heven : 2 ∣ k * (k - 1) := by
      cases k with
      | zero => simp
      | succ j => simpa [Nat.succ_sub_one, mul_comm] using (Nat.even_mul_succ_self j).two_dvd
    have h2 : ((k * (k - 1) / 2 : ℕ) : ℝ) * 2 = ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
      exact_mod_cast (by rw [mul_comm]; exact Nat.mul_div_cancel' heven : (k * (k - 1) / 2) * 2 = k * (k - 1))
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
    have hden_pos : (0 : ℝ) < ((k * (k - 1) / 2 : ℕ) : ℝ) := by nlinarith
    rw [div_eq_div_iff (ne_of_gt hden_pos) (ne_of_gt hk_pos)]
    linarith
  rw [hratio m hm3, hratio n hn]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm : (n : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact div_lt_div_of_pos_left (by norm_num) hn_pos hnm
