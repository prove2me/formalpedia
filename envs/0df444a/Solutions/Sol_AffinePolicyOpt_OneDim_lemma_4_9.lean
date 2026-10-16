-- Prove2me | solution 1 for AffinePolicyOpt.OneDim.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T11:37:44.777348+00:00
-- url     : https://prove2.me/submissions/469a7f05-ceef-42a8-ba54-5a0176d7eeac

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

namespace P3c26

open AffinePolicyOpt.OneDim Set

lemma incr_mono {h : ℝ → ℝ} (hh : ConvexOn ℝ univ h) {u v x : ℝ} (hx : 0 ≤ x) (huv : u ≤ v) :
    h (u + x) - h u ≤ h (v + x) - h v := by
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0]; simp
  · have hd : 0 < v + x - u := by linarith
    have hα0 : 0 ≤ x / (v + x - u) := div_nonneg hx hd.le
    have hβ0 : 0 ≤ (v - u) / (v + x - u) := div_nonneg (by linarith) hd.le
    have hsum : (x / (v + x - u)) + ((v - u) / (v + x - u)) = 1 := by
      field_simp; ring
    have hsum' : ((v - u) / (v + x - u)) + (x / (v + x - u)) = 1 := by linarith
    have h1 := hh.2 (mem_univ u) (mem_univ (v + x)) hβ0 hα0 hsum'
    have h2 := hh.2 (mem_univ u) (mem_univ (v + x)) hα0 hβ0 hsum
    have e1 : ((v - u) / (v + x - u)) • u + (x / (v + x - u)) • (v + x) = u + x := by
      simp only [smul_eq_mul]; field_simp; ring
    have e2 : (x / (v + x - u)) • u + ((v - u) / (v + x - u)) • (v + x) = v := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    simp only [smul_eq_mul] at h1 h2
    set α := x / (v + x - u)
    set β := (v - u) / (v + x - u)
    have : β * h u + α * h (v + x) + (α * h u + β * h (v + x)) = h u + h (v + x) := by
      have : β + α = 1 := hsum'
      calc _ = (β + α) * h u + (α + β) * h (v + x) := by ring
        _ = _ := by rw [hsum', hsum]; ring
    linarith

lemma psum_add {n : ℕ} (x : Fin n → ℝ) (p q r : ℕ) (hpq : p ≤ q) (hqr : q ≤ r) :
    psum x p q + psum x q r = psum x p r := by
  unfold psum
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h1 : p ≤ (g : ℕ) ∧ (g : ℕ) < q
  · have h2 : ¬ (q ≤ (g : ℕ) ∧ (g : ℕ) < r) := by omega
    have h3 : p ≤ (g : ℕ) ∧ (g : ℕ) < r := by omega
    simp [h1, h2, h3]
  · by_cases h2 : q ≤ (g : ℕ) ∧ (g : ℕ) < r
    · have h3 : p ≤ (g : ℕ) ∧ (g : ℕ) < r := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (p ≤ (g : ℕ) ∧ (g : ℕ) < r) := by omega
      simp [h1, h2, h3]

lemma psum_self {n : ℕ} (x : Fin n → ℝ) (p : ℕ) : psum x p p = 0 := by
  unfold psum
  have : Finset.univ.filter (fun g : Fin n => p ≤ (g : ℕ) ∧ (g : ℕ) < p) = ∅ := by
    ext g; simp
  rw [this]; simp

lemma psum_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ g, 0 ≤ x g) (p q : ℕ) : 0 ≤ psum x p q :=
  Finset.sum_nonneg (fun g _ => hx g)

lemma psum_le {n : ℕ} {x y : Fin n → ℝ} (hxy : ∀ g, x g ≤ y g) (p q : ℕ) :
    psum x p q ≤ psum y p q :=
  Finset.sum_le_sum (fun g _ => hxy g)

lemma psum_congr {n : ℕ} {x y : Fin n → ℝ} (p q : ℕ)
    (h : ∀ g : Fin n, p ≤ (g : ℕ) → (g : ℕ) < q → x g = y g) : psum x p q = psum y p q := by
  unfold psum
  apply Finset.sum_congr rfl
  intro g hg
  simp only [Finset.mem_filter] at hg
  exact h g hg.2.1 hg.2.2

lemma psum_lin {n : ℕ} (K : ℝ) (a b : Fin n → ℝ) (p q : ℕ) :
    psum (fun g => K * b g - a g) p q = K * psum b p q - psum a p q := by
  unfold psum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- reindexed block `[p, p+m)` as a vector of length `m`. -/
def blk {N : ℕ} (x : Fin N → ℝ) (p m : ℕ) (h : p + m ≤ N) : Fin m → ℝ :=
  fun j => x ⟨p + j, by have := j.2; omega⟩

lemma sum_blk {N : ℕ} (x : Fin N → ℝ) (p m : ℕ) (h : p + m ≤ N) (j : ℕ) (hj : j ≤ m) :
    ∑ i : Fin m, (if (i : ℕ) < j then blk x p m h i else 0) = psum x p (p + j) := by
  unfold psum
  rw [Finset.sum_filter]
  let ι : Fin m → Fin N := fun i => ⟨p + i, by have := i.2; omega⟩
  have hinj : Function.Injective ι := by
    intro i1 i2 h12
    have : p + (i1 : ℕ) = p + (i2 : ℕ) := congrArg Fin.val h12
    exact Fin.ext (by omega)
  set G : Fin N → ℝ := fun g => if p ≤ (g : ℕ) ∧ (g : ℕ) < p + j then x g else 0 with hG
  have h1 : ∀ i : Fin m, (if (i : ℕ) < j then blk x p m h i else 0) = G (ι i) := by
    intro i
    simp only [hG, blk, ι]
    by_cases hij : (i : ℕ) < j
    · simp [hij]
    · have : ¬ (p ≤ p + (i : ℕ) ∧ p + (i : ℕ) < p + j) := by omega
      simp [hij, this]
  simp_rw [h1]
  rw [← Finset.sum_image (f := G) (fun i _ j _ hij => hinj hij)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro g _ hg
  simp only [hG]
  have : ¬ (p ≤ (g : ℕ) ∧ (g : ℕ) < p + j) := by
    intro hc
    apply hg
    rw [Finset.mem_image]
    refine ⟨⟨(g : ℕ) - p, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext; simp [ι]; omega
  simp [this]

lemma block_dom (m : ℕ) (a b : Fin m → ℝ) (hab : GenOrdered a b) (ψ : ℝ → ℝ)
    (hψ : ConvexOn ℝ univ ψ) (K : ℝ)
    (hpre : ∀ j ≤ m, ψ (∑ i, b i * prefixVertex m j i) + ∑ i, a i * prefixVertex m j i ≤
        K * ∑ i, b i * prefixVertex m j i)
    (w : Fin m → ℝ) (hw : w ∈ cube m) :
    ψ (∑ i, b i * w i) + ∑ i, a i * w i ≤ K * ∑ i, b i * w i := by
  have hf : ConvexOn ℝ univ (fun x => ψ x - K * x) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    have := hψ.2 (mem_univ x) (mem_univ y) hs ht hst
    simp only [smul_eq_mul] at this ⊢
    nlinarith [this, hst]
  obtain ⟨n, hn, hmax⟩ := P818.lemma_4_1 m 0 0 a b hab (fun x => ψ x - K * x) hf
  have h1 := (isMaxOn_iff.1 hmax) w hw
  have h2 := hpre n hn
  simp only [zon, zero_add] at h1
  linarith [h1, h2]

lemma block_claim {N : ℕ} (a b : Fin N → ℝ) (hab : GenOrdered a b) (ψ : ℝ → ℝ)
    (hψ : ConvexOn ℝ univ ψ) (K : ℝ) (p m : ℕ) (hpm : p + m ≤ N)
    (hpre : ∀ j ≤ m, ψ (psum b p (p + j)) + psum a p (p + j) ≤ K * psum b p (p + j))
    (w : Fin N → ℝ) (hw : w ∈ cube N) :
    ψ (psum (fun g => b g * w g) p (p + m)) + psum (fun g => a g * w g) p (p + m) ≤
      K * psum (fun g => b g * w g) p (p + m) := by
  have hGen : GenOrdered (blk a p m hpm) (blk b p m hpm) := by
    refine ⟨fun i => hab.1 _, fun i j hij => hab.2 _ _ ?_⟩
    have : (i : ℕ) < (j : ℕ) := hij
    show (⟨p + i, _⟩ : Fin N) < ⟨p + j, _⟩
    rw [Fin.lt_def]; simp only; omega
  have hwB : blk w p m hpm ∈ cube m := fun i => hw _
  have e : ∀ x : Fin N → ℝ, ∀ j ≤ m,
      ∑ i, blk x p m hpm i * prefixVertex m j i = psum x p (p + j) := by
    intro x j hj
    rw [← sum_blk x p m hpm j hj]
    apply Finset.sum_congr rfl
    intro i _
    unfold prefixVertex
    split_ifs <;> simp
  have efull : ∀ x : Fin N → ℝ, ∑ i, blk x p m hpm i = psum x p (p + m) := by
    intro x
    rw [← sum_blk x p m hpm m le_rfl]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.2]
  have := block_dom m (blk a p m hpm) (blk b p m hpm) hGen ψ hψ K
    (fun j hj => by rw [e b j hj, e a j hj]; exact hpre j hj) (blk w p m hpm) hwB
  have e1 : ∑ i, blk b p m hpm i * blk w p m hpm i = psum (fun g => b g * w g) p (p + m) :=
    efull (fun g => b g * w g)
  have e2 : ∑ i, blk a p m hpm i * blk w p m hpm i = psum (fun g => a g * w g) p (p + m) :=
    efull (fun g => a g * w g)
  rw [e1, e2] at this
  exact this

lemma convex_shift_sub {h : ℝ → ℝ} (hh : ConvexOn ℝ univ h) (c : ℝ) :
    ConvexOn ℝ univ (fun y => h (c + y) - h c) := by
  refine ⟨convex_univ, fun u _ v _ s1 t1 hs1 ht1 hst1 => ?_⟩
  have := hh.2 (mem_univ (c + u)) (mem_univ (c + v)) hs1 ht1 hst1
  simp only [smul_eq_mul] at this ⊢
  have e : s1 * (c + u) + t1 * (c + v) = c + (s1 * u + t1 * v) := by
    calc _ = (s1 + t1) * c + (s1 * u + t1 * v) := by ring
      _ = _ := by rw [hst1, one_mul]
  rw [e] at this
  have hc : (s1 + t1) * h c = h c := by rw [hst1, one_mul]
  nlinarith [this, hc]

lemma psum_all {n : ℕ} (x : Fin n → ℝ) (q : ℕ) (hq : n ≤ q) : psum x 0 q = ∑ g, x g := by
  unfold psum
  rw [Finset.filter_true_of_mem]
  intro g _
  exact ⟨Nat.zero_le _, lt_of_lt_of_le g.2 hq⟩

theorem lemma_4_9 (k : ℕ) (b0 : ℝ) (a b : Fin (k + 1) → ℝ) (hb : ∀ g, 0 < b g)
    (hab : GenOrdered a b) (h : ℝ → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (z0 : ℝ) (z : Fin (k + 1) → ℝ)
    (n : ℕ) (s : Fin (n + 1) → ℕ) (hs : StrictMono s) (hs0 : s 0 = 0)
    (hsn : s (Fin.last n) = k + 1) (K : Fin n → ℝ)
    (h51m : ∀ i, z0 + psum z 0 (s i) = h (b0 + psum b 0 (s i)))
    (h51a : ∀ i : Fin n, ∀ g : Fin (k + 1), s i.castSucc ≤ (g : ℕ) → (g : ℕ) < s i.succ →
      z g + a g = K i * b g)
    (h52 : Antitone K)
    (h53 : ∀ i : Fin n, ∀ j : ℕ, s i.castSucc < j → j < s i.succ →
      h (b0 + psum b 0 j) - h (b0 + psum b 0 (s i.castSucc)) + psum a (s i.castSucc) j ≤
          K i * psum b (s i.castSucc) j ∧
        K i * psum b j (s i.succ) ≤
          h (b0 + psum b 0 (s i.succ)) - h (b0 + psum b 0 j) + psum a j (s i.succ)) :
    ∀ w ∈ cube (k + 1), h (b0 + ∑ i, b i * w i) ≤ z0 + ∑ i, z i * w i := by
  intro w hw
  have key : ∀ i : Fin (n + 1), h (b0 + psum (fun g => b g * w g) 0 (s i)) ≤
      z0 + psum (fun g => z g * w g) 0 (s i) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [hs0, psum_self, psum_self]
      have := h51m 0
      rw [hs0, psum_self, psum_self] at this
      linarith
    | succ i ih =>
      have hpq : s i.castSucc < s i.succ := hs (Fin.castSucc_lt_succ)
      set p := s i.castSucc with hp
      set q := s i.succ with hq
      have hqN : q ≤ k + 1 := by
        have := hs.monotone (Fin.le_last i.succ)
        rw [hsn] at this; exact this
      have hbw : ∀ g, 0 ≤ b g * w g := fun g => mul_nonneg (hb g).le (hw g).1
      have hbwle : ∀ g, b g * w g ≤ b g := fun g => by nlinarith [hb g, (hw g).2]
      set x := psum (fun g => b g * w g) p q with hx
      set X := psum (fun g => b g * w g) 0 p with hX
      have hx0 : 0 ≤ x := psum_nonneg hbw _ _
      have hXle : X ≤ psum b 0 p := psum_le hbwle _ _
      have hPQ : psum (fun g => b g * w g) 0 q = X + x := (psum_add _ 0 p q (Nat.zero_le _) hpq.le).symm
      -- Step A
      have hA := incr_mono hh hx0 (show b0 + X ≤ b0 + psum b 0 p by linarith)
      -- alignment on block
      have hZ : psum z p q = K i * psum b p q - psum a p q := by
        rw [← psum_lin (K i) a b p q]
        exact psum_congr p q (fun g h1 h2 => by have := h51a i g h1 h2; linarith)
      have hZw : psum (fun g => z g * w g) p q =
          K i * psum (fun g => b g * w g) p q - psum (fun g => a g * w g) p q := by
        rw [← psum_lin (K i) (fun g => a g * w g) (fun g => b g * w g) p q]
        exact psum_congr p q (fun g h1 h2 => by
          have := h51a i g h1 h2
          have : z g = K i * b g - a g := by linarith
          rw [this]; ring)
      have hPp : psum b 0 q = psum b 0 p + psum b p q := (psum_add b 0 p q (Nat.zero_le _) hpq.le).symm
      -- hpre for block_claim
      have hpre : ∀ j ≤ q - p, (fun y => h (b0 + psum b 0 p + y) - h (b0 + psum b 0 p))
          (psum b p (p + j)) + psum a p (p + j) ≤ K i * psum b p (p + j) := by
        intro j hj
        have hjq : p + j ≤ q := by omega
        have hsplit : psum b 0 (p + j) = psum b 0 p + psum b p (p + j) :=
          (psum_add b 0 p (p + j) (Nat.zero_le _) (by omega)).symm
        simp only
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          simp [psum_self]
        · rcases lt_or_eq_of_le hjq with hlt | heq
          · have := (h53 i (p + j) (by omega) hlt).1
            rw [hsplit] at this
            have e : b0 + psum b 0 p + psum b p (p + j) = b0 + (psum b 0 p + psum b p (p + j)) := by ring
            rw [e]
            linarith
          · have e1 := h51m i.succ
            have e2 := h51m i.castSucc
            have e3 : psum z 0 q = psum z 0 p + psum z p q :=
              (psum_add z 0 p q (Nat.zero_le _) hpq.le).symm
            have hjeq : p + j = q := heq
            rw [hjeq]
            have e : b0 + psum b 0 p + psum b p q = b0 + psum b 0 q := by rw [hPp]; ring
            rw [e]
            rw [← hq] at e1
            rw [← hp] at e2
            linarith
      have hB := block_claim a b hab (fun y => h (b0 + psum b 0 p + y) - h (b0 + psum b 0 p))
        (convex_shift_sub hh (b0 + psum b 0 p))
        (K i) p (q - p) (by omega) hpre w hw
      have hqp : p + (q - p) = q := by omega
      rw [hqp] at hB
      have := ih
      rw [hPQ]
      have hzs : psum (fun g => z g * w g) 0 q = psum (fun g => z g * w g) 0 p + psum (fun g => z g * w g) p q :=
        (psum_add _ 0 p q (Nat.zero_le _) hpq.le).symm
      rw [hzs]
      rw [← hx] at hB
      have e : b0 + X + x = b0 + (X + x) := by ring
      rw [← e]
      have hA' : h (b0 + X + x) - h (b0 + X) ≤ h (b0 + psum b 0 p + x) - h (b0 + psum b 0 p) := hA
      linarith [hB, hZw, ih, hA']
  have hfin := key (Fin.last n)
  rw [hsn, psum_all _ _ le_rfl, psum_all _ _ le_rfl] at hfin
  exact hfin

end P3c26

open AffinePolicyOpt.OneDim in
theorem solution (k : ℕ) (b0 : ℝ) (a b : Fin (k + 1) → ℝ) (hb : ∀ g, 0 < b g)
    (hab : GenOrdered a b) (h : ℝ → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (z0 : ℝ) (z : Fin (k + 1) → ℝ)
    (n : ℕ) (s : Fin (n + 1) → ℕ) (hs : StrictMono s) (hs0 : s 0 = 0)
    (hsn : s (Fin.last n) = k + 1) (K : Fin n → ℝ)
    -- (51), matching
    (h51m : ∀ i, z0 + psum z 0 (s i) = h (b0 + psum b 0 (s i)))
    -- (51), alignment, cross-multiplied
    (h51a : ∀ i : Fin n, ∀ g : Fin (k + 1), s i.castSucc ≤ (g : ℕ) → (g : ℕ) < s i.succ →
      z g + a g = K i * b g)
    -- (52)
    (h52 : Antitone K)
    -- (53), cross-multiplied
    (h53 : ∀ i : Fin n, ∀ j : ℕ, s i.castSucc < j → j < s i.succ →
      h (b0 + psum b 0 j) - h (b0 + psum b 0 (s i.castSucc)) + psum a (s i.castSucc) j ≤
          K i * psum b (s i.castSucc) j ∧
        K i * psum b j (s i.succ) ≤
          h (b0 + psum b 0 (s i.succ)) - h (b0 + psum b 0 j) + psum a j (s i.succ)) :
    ∀ w ∈ cube (k + 1), h (b0 + ∑ i, b i * w i) ≤ z0 + ∑ i, z i * w i := by
  exact P3c26.lemma_4_9 k b0 a b hb hab h hh z0 z n s hs hs0 hsn K h51m h51a h52 h53
