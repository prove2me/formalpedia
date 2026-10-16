-- Prove2me | solution 1 for AffinePolicyOpt.OneDim.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T11:23:48.995641+00:00
-- url     : https://prove2.me/submissions/451530ba-e834-46c6-bacf-bfad133d3cb3

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

set_option autoImplicit false

namespace P818

open AffinePolicyOpt.OneDim Set

variable {k : ℕ}

lemma prefix_succ (j : ℕ) (i : Fin k) :
    prefixVertex k (j + 1) i = prefixVertex k j i + (if (i : ℕ) = j then 1 else 0) := by
  unfold prefixVertex
  by_cases h1 : (i : ℕ) < j
  · simp [h1, show (i : ℕ) < j + 1 by omega, show ¬ (i : ℕ) = j by omega]
  · by_cases h2 : (i : ℕ) = j
    · simp [h2]
    · simp [h1, h2, show ¬ (i : ℕ) < j + 1 by omega]

lemma sum_ite_idx (j : ℕ) (hj : j < k) (c : Fin k → ℝ) :
    ∑ i, c i * (if (i : ℕ) = j then (1 : ℝ) else 0) = c ⟨j, hj⟩ := by
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin k)]
  · simp
  · intro i _ hi
    have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma zon_prefix_succ (a0 b0 : ℝ) (a b : Fin k → ℝ) (j : ℕ) (hj : j < k) :
    (zon a0 b0 a b (prefixVertex k (j + 1))).1 =
        (zon a0 b0 a b (prefixVertex k j)).1 + a ⟨j, hj⟩ ∧
    (zon a0 b0 a b (prefixVertex k (j + 1))).2 =
        (zon a0 b0 a b (prefixVertex k j)).2 + b ⟨j, hj⟩ := by
  constructor
  · unfold zon
    simp only [prefix_succ, mul_add, Finset.sum_add_distrib, sum_ite_idx j hj a]
    ring
  · unfold zon
    simp only [prefix_succ, mul_add, Finset.sum_add_distrib, sum_ite_idx j hj b]
    ring

lemma support_line (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b) (j : ℕ) (hj : j < k)
    (w : Fin k → ℝ) (hw : w ∈ cube k) :
    b ⟨j, hj⟩ * ((zon a0 b0 a b w).1 - (zon a0 b0 a b (prefixVertex k j)).1) ≤
      a ⟨j, hj⟩ * ((zon a0 b0 a b w).2 - (zon a0 b0 a b (prefixVertex k j)).2) := by
  have h1 : (zon a0 b0 a b w).1 - (zon a0 b0 a b (prefixVertex k j)).1 =
      ∑ i, a i * (w i - prefixVertex k j i) := by
    unfold zon; simp only [mul_sub, Finset.sum_sub_distrib]; ring
  have h2 : (zon a0 b0 a b w).2 - (zon a0 b0 a b (prefixVertex k j)).2 =
      ∑ i, b i * (w i - prefixVertex k j i) := by
    unfold zon; simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [h1, h2]
  have hsum : b ⟨j, hj⟩ * (∑ i, a i * (w i - prefixVertex k j i)) -
      a ⟨j, hj⟩ * (∑ i, b i * (w i - prefixVertex k j i)) =
      ∑ i, (b ⟨j, hj⟩ * a i - a ⟨j, hj⟩ * b i) * (w i - prefixVertex k j i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intros; ring
  have hnp : ∑ i, (b ⟨j, hj⟩ * a i - a ⟨j, hj⟩ * b i) * (w i - prefixVertex k j i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have hwi := hw i
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · have hij : i < ⟨j, hj⟩ := h
      have hord := hab.2 i ⟨j, hj⟩ hij
      have hp : prefixVertex k j i = 1 := by unfold prefixVertex; simp [h]
      rw [hp]
      nlinarith [hwi.2]
    · have : i = ⟨j, hj⟩ := Fin.ext h
      subst this
      have e : b ⟨j, hj⟩ * a ⟨j, hj⟩ - a ⟨j, hj⟩ * b ⟨j, hj⟩ = 0 := by ring
      rw [e, zero_mul]
    · have hij : (⟨j, hj⟩ : Fin k) < i := h
      have hord := hab.2 ⟨j, hj⟩ i hij
      have hp : prefixVertex k j i = 0 := by unfold prefixVertex; simp; omega
      rw [hp]
      nlinarith [hwi.1]
  linarith

lemma exists_pair (s : ℕ → ℝ) (b : Fin k → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hs : ∀ j (hj : j < k), s (j + 1) = s j + b ⟨j, hj⟩) (t : ℝ) (h0 : s 0 ≤ t)
    (hk : t ≤ s k) (hpos : s 0 < s k) :
    ∃ j, ∃ hj : j < k, 0 < b ⟨j, hj⟩ ∧ s j ≤ t ∧ t ≤ s j + b ⟨j, hj⟩ := by
  by_contra hne
  have hne' : ∀ j (hj : j < k), 0 < b ⟨j, hj⟩ → s j ≤ t → s j + b ⟨j, hj⟩ < t := by
    intro j hj h1 h2
    by_contra h3
    exact hne ⟨j, hj, h1, h2, not_lt.1 h3⟩
  have P : ∀ n, n ≤ k → s n ≤ t ∧ (s 0 < s n → s n < t) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨h0, fun h => absurd h (lt_irrefl _)⟩
    | succ n ih =>
      intro hn
      have hnk : n < k := hn
      obtain ⟨h1, h2⟩ := ih hnk.le
      rw [hs n hnk]
      rcases (hb ⟨n, hnk⟩).eq_or_lt with h | h
      · rw [← h, add_zero]; exact ⟨h1, h2⟩
      · have := hne' n hnk h h1
        exact ⟨this.le, fun _ => this⟩
  obtain ⟨_, h2⟩ := P k le_rfl
  have := h2 hpos
  linarith


lemma dominated (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ univ f) (w : Fin k → ℝ) (hw : w ∈ cube k) (hpos : ∃ i, 0 < b i) :
    ∃ n ≤ k, (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2 ≤
      (zon a0 b0 a b (prefixVertex k n)).1 + f (zon a0 b0 a b (prefixVertex k n)).2 := by
  have hb : ∀ i, 0 ≤ b i := hab.1
  have hs0 : (zon a0 b0 a b (prefixVertex k 0)).2 = b0 := by simp [zon, prefixVertex]
  have hsk : (zon a0 b0 a b (prefixVertex k k)).2 = b0 + ∑ i, b i := by
    show b0 + ∑ i, b i * prefixVertex k k i = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [prefixVertex, i.isLt]
  have ht : (zon a0 b0 a b w).2 = b0 + ∑ i, b i * w i := rfl
  have h0 : (zon a0 b0 a b (prefixVertex k 0)).2 ≤ (zon a0 b0 a b w).2 := by
    rw [hs0, ht]
    have : 0 ≤ ∑ i, b i * w i := Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (hw i).1)
    linarith
  have hk : (zon a0 b0 a b w).2 ≤ (zon a0 b0 a b (prefixVertex k k)).2 := by
    rw [hsk, ht]
    have : ∑ i, b i * w i ≤ ∑ i, b i :=
      Finset.sum_le_sum (fun i _ => by nlinarith [hb i, (hw i).2])
    linarith
  have hpos' : (zon a0 b0 a b (prefixVertex k 0)).2 < (zon a0 b0 a b (prefixVertex k k)).2 := by
    rw [hs0, hsk]
    obtain ⟨i0, hi0⟩ := hpos
    have : 0 < ∑ i, b i := Finset.sum_pos' (fun i _ => hb i) ⟨i0, Finset.mem_univ _, hi0⟩
    linarith
  obtain ⟨j, hj, hbj, hsj, hjt⟩ := exists_pair (fun n => (zon a0 b0 a b (prefixVertex k n)).2) b hb
    (fun j hj => (zon_prefix_succ a0 b0 a b j hj).2) _ h0 hk hpos'
  obtain ⟨hv1, hv2⟩ := zon_prefix_succ a0 b0 a b j hj
  set t := (zon a0 b0 a b w).2 with htdef
  set sj := (zon a0 b0 a b (prefixVertex k j)).2 with hsjdef
  set lam := (t - sj) / b ⟨j, hj⟩ with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hbj.le
  have hlam1 : lam ≤ 1 := (div_le_one hbj).2 (by linarith)
  have hlamb : lam * b ⟨j, hj⟩ = t - sj := div_mul_cancel₀ _ hbj.ne'
  have hSL := support_line a0 b0 a b hab j hj w hw
  have h1w : (zon a0 b0 a b w).1 ≤ (zon a0 b0 a b (prefixVertex k j)).1 + lam * a ⟨j, hj⟩ := by
    have h3 : b ⟨j, hj⟩ * ((zon a0 b0 a b w).1 - (zon a0 b0 a b (prefixVertex k j)).1) ≤
        b ⟨j, hj⟩ * (lam * a ⟨j, hj⟩) := by
      have : a ⟨j, hj⟩ * (t - sj) = b ⟨j, hj⟩ * (lam * a ⟨j, hj⟩) := by
        rw [← hlamb]; ring
      linarith
    have := le_of_mul_le_mul_left h3 hbj
    linarith
  have hfc := hf.2 (mem_univ sj) (mem_univ ((zon a0 b0 a b (prefixVertex k (j + 1))).2))
    (sub_nonneg.2 hlam1) hlam0 (by ring : (1 - lam) + lam = 1)
  have hts : (1 - lam) • sj + lam • (zon a0 b0 a b (prefixVertex k (j + 1))).2 = t := by
    simp only [smul_eq_mul]; rw [hv2]; nlinarith [hlamb]
  rw [hts] at hfc
  simp only [smul_eq_mul] at hfc
  rw [hv2] at hfc
  have hF : (zon a0 b0 a b w).1 + f t ≤
      (1 - lam) * ((zon a0 b0 a b (prefixVertex k j)).1 + f sj) +
      lam * ((zon a0 b0 a b (prefixVertex k (j + 1))).1 +
        f ((zon a0 b0 a b (prefixVertex k j)).2 + b ⟨j, hj⟩)) := by
    rw [hv1]; nlinarith [h1w, hfc]
  rcases le_total ((zon a0 b0 a b (prefixVertex k (j + 1))).1 +
        f (zon a0 b0 a b (prefixVertex k (j + 1))).2)
      ((zon a0 b0 a b (prefixVertex k j)).1 + f sj) with h | h
  · refine ⟨j, hj.le, ?_⟩
    rw [hv2] at h
    nlinarith [mul_nonneg hlam0 (sub_nonneg.2 h)]
  · refine ⟨j + 1, hj, ?_⟩
    rw [hv2] at h ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hlam1) (sub_nonneg.2 h)]

lemma caseB (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b) (f : ℝ → ℝ)
    (w : Fin k → ℝ) (hw : w ∈ cube k) (hz : ∀ i, b i = 0) :
    ∃ n ≤ k, (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2 ≤
      (zon a0 b0 a b (prefixVertex k n)).1 + f (zon a0 b0 a b (prefixVertex k n)).2 := by
  by_cases hk2 : 2 ≤ k
  · exfalso
    have := hab.2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
    simp [hz] at this
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact ⟨0, le_rfl, by simp [zon]⟩
    · rcases le_total 0 (a 0) with h | h
      · refine ⟨1, le_rfl, ?_⟩
        simp [zon, prefixVertex, hz]
        nlinarith [(hw 0).2, (hw 0).1]
      · refine ⟨0, Nat.zero_le _, ?_⟩
        simp [zon, prefixVertex, hz]
        nlinarith [(hw 0).2, (hw 0).1]

theorem lemma_4_1 (k : ℕ) (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ∃ n ≤ k, IsMaxOn (fun w => (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2)
      (cube k) (prefixVertex k n) := by
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image (Finset.range (k + 1))
    (fun n => (zon a0 b0 a b (prefixVertex k n)).1 + f (zon a0 b0 a b (prefixVertex k n)).2)
    ⟨0, by simp⟩
  refine ⟨n, by simpa [Nat.lt_succ_iff] using hn, ?_⟩
  intro w hw
  show (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2 ≤
    (zon a0 b0 a b (prefixVertex k n)).1 + f (zon a0 b0 a b (prefixVertex k n)).2
  have hdom : ∃ m ≤ k, (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2 ≤
      (zon a0 b0 a b (prefixVertex k m)).1 + f (zon a0 b0 a b (prefixVertex k m)).2 := by
    by_cases hpos : ∃ i, 0 < b i
    · exact dominated a0 b0 a b hab f hf w hw hpos
    · exact caseB a0 b0 a b hab f w hw
        (fun i => le_antisymm (not_lt.1 (fun h => hpos ⟨i, h⟩)) (hab.1 i))
  obtain ⟨m, hm, hle⟩ := hdom
  exact hle.trans (hmax m (Finset.mem_range.2 (by omega)))

end P818

open AffinePolicyOpt.OneDim in
theorem solution (k : ℕ) (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : GenOrdered a b)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ∃ n ≤ k, IsMaxOn (fun w => (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2)
      (cube k) (prefixVertex k n) := by
  exact P818.lemma_4_1 k a0 b0 a b hab f hf
