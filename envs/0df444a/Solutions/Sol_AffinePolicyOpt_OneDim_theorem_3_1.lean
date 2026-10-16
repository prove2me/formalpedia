-- Prove2me | solution 1 for AffinePolicyOpt.OneDim.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:45:38.345784+00:00
-- url     : https://prove2.me/submissions/ec6b3ab5-ed2e-48a4-87bf-e5d8662bf161

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Setting
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

set_option autoImplicit false



/-! Generic upper-hull lemma (172ae934 stage_step, piece GHL).
Points `(x j, y j)` with `x` monotone. From a start `v` that is the top of its column,
the "farthest max-slope" rule builds hull vertices `s 0 = v < s 1 < ... < s m ≤ n` with strictly
increasing `x`, antitone segment slopes, every intermediate point weakly below its segment,
and every point after `s m` in the same column as `s m` and not above it. -/

namespace P172H

noncomputable def sl (x y : ℕ → ℝ) (i j : ℕ) : ℝ := (y j - y i) / (x j - x i)

lemma sl_spec (x y : ℕ → ℝ) (i j : ℕ) (h : x i < x j) :
    y j - y i = sl x y i j * (x j - x i) := by
  unfold sl
  rw [div_mul_cancel₀ _ (sub_ne_zero.2 (ne_of_gt h))]

lemma sl_le_of_below (x y : ℕ → ℝ) (i j : ℕ) (K : ℝ) (h : x i < x j)
    (hb : y j - y i ≤ K * (x j - x i)) : sl x y i j ≤ K := by
  unfold sl
  rw [div_le_iff₀ (sub_pos.2 h)]
  linarith

lemma below_of_sl_le (x y : ℕ → ℝ) (i j : ℕ) (K : ℝ) (h : x i < x j)
    (hs : sl x y i j ≤ K) : y j - y i ≤ K * (x j - x i) := by
  rw [sl_spec x y i j h]
  exact mul_le_mul_of_nonneg_right hs (sub_pos.2 h).le

/-- Hull data from `v` inside `[v, n]`. -/
def HullFrom (x y : ℕ → ℝ) (n v m : ℕ) (s : ℕ → ℕ) : Prop :=
  s 0 = v ∧ (∀ i ≤ m, v ≤ s i ∧ s i ≤ n) ∧ (∀ i < m, s i < s (i + 1)) ∧
  (∀ i < m, x (s i) < x (s (i + 1))) ∧
  (∀ i, i + 1 < m → sl x y (s (i + 1)) (s (i + 2)) ≤ sl x y (s i) (s (i + 1))) ∧
  (∀ i < m, ∀ j, s i < j → j < s (i + 1) →
      y j - y (s i) ≤ sl x y (s i) (s (i + 1)) * (x j - x (s i))) ∧
  (∀ j, s m < j → j ≤ n → x j = x (s m) ∧ y j ≤ y (s m))

theorem hull_exists (x y : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∀ d v, n - v = d → v ≤ n → (∀ j, v < j → j ≤ n → x j = x v → y j ≤ y v) →
      ∃ m s, HullFrom x y n v m s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro v hd hvn hgood
  classical
  by_cases hS : ∃ j, v < j ∧ j ≤ n ∧ x v < x j
  · set S := (Finset.Ioc v n).filter (fun j => x v < x j) with hSdef
    have hmemS : ∀ j, j ∈ S ↔ (v < j ∧ j ≤ n) ∧ x v < x j := by
      intro j; simp [hSdef, Finset.mem_Ioc]
    have hSne : S.Nonempty := by
      obtain ⟨j, h1, h2, h3⟩ := hS
      exact ⟨j, (hmemS j).2 ⟨⟨h1, h2⟩, h3⟩⟩
    obtain ⟨j0, hj0S, hmax⟩ := S.exists_max_image (sl x y v) hSne
    set σ := sl x y v j0 with hσ
    set Tset := S.filter (fun j => sl x y v j = σ) with hTdef
    have hTne : Tset.Nonempty := ⟨j0, Finset.mem_filter.2 ⟨hj0S, hσ.symm⟩⟩
    set u := Tset.max' hTne with hudef
    have huT : u ∈ Tset := Tset.max'_mem hTne
    have huS : u ∈ S := (Finset.mem_filter.1 huT).1
    have husl : sl x y v u = σ := (Finset.mem_filter.1 huT).2
    obtain ⟨⟨hvu, hun⟩, hxvu⟩ := (hmemS u).1 huS
    have hfar : ∀ j ∈ S, sl x y v j = σ → j ≤ u :=
      fun j hj he => Tset.le_max' j (by simp [hTdef, hj, he])
    have hyu : y u - y v = σ * (x u - x v) := by rw [← husl]; exact sl_spec x y v u hxvu
    have hgood_u : ∀ j, u < j → j ≤ n → x j = x u → y j ≤ y u := by
      intro j huj hjn hxj
      have hjS : j ∈ S := (hmemS j).2 ⟨⟨by omega, hjn⟩, by rw [hxj]; exact hxvu⟩
      have hle : sl x y v j ≤ σ := hmax j hjS
      have hb := below_of_sl_le x y v j σ (by rw [hxj]; exact hxvu) hle
      rw [hxj] at hb
      linarith
    obtain ⟨m', s', hH⟩ := ih (n - u) (by omega) u rfl hun hgood_u
    obtain ⟨h0, hrng, hinc, hxinc, hanti, hbel, hlast⟩ := hH
    refine ⟨m' + 1, fun i => if i = 0 then v else s' (i - 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi
      rcases i with _ | i
      · simp; exact hvn
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        have := hrng i (by omega)
        omega
    · intro i hi
      rcases i with _ | i
      · simp; rw [h0]; exact hvu
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact hinc i (by omega)
    · intro i hi
      rcases i with _ | i
      · simp; rw [h0]; exact hxvu
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact hxinc i (by omega)
    · intro i hi
      rcases i with _ | i
      · simp only [Nat.zero_add, Nat.one_ne_zero, if_false, if_true, show (2:ℕ) ≠ 0 by omega,
          show (1:ℕ) - 1 = 0 from rfl, show (2:ℕ) - 1 = 1 from rfl]
        rw [h0, husl]
        have hm1 : 0 < m' := by omega
        have hx1 : x u < x (s' 1) := by have := hxinc 0 hm1; rw [h0] at this; exact this
        have hr1 := hrng 1 (by omega)
        have h1S : s' 1 ∈ S := (hmemS _).2 ⟨⟨by omega, hr1.2⟩, lt_trans hxvu hx1⟩
        have hb := below_of_sl_le x y v (s' 1) σ (lt_trans hxvu hx1) (hmax _ h1S)
        apply sl_le_of_below x y u (s' 1) σ hx1
        linarith
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
          show i + 1 + 1 - 1 = i + 1 by omega, show i + 2 - 1 = i + 1 by omega,
          show i + 1 + 2 - 1 = i + 2 by omega]
        exact hanti i (by omega)
    · intro i hi j hj1 hj2
      rcases i with _ | i
      · simp only [if_true, Nat.zero_add, Nat.one_ne_zero, if_false] at hj1 hj2 ⊢
        simp only [show (1:ℕ) - 1 = 0 from rfl, h0] at hj2 ⊢
        rw [husl]
        rcases (hx hj1.le).eq_or_lt with he | hlt
        · have := hgood j hj1 (by omega) he.symm
          rw [← he]; linarith
        · have hjS : j ∈ S := (hmemS j).2 ⟨⟨hj1, by omega⟩, hlt⟩
          exact below_of_sl_le x y v j σ hlt (hmax j hjS)
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj1 hj2 ⊢
        exact hbel i (by omega) j hj1 hj2
    · intro j hj hjn
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj ⊢
      exact hlast j hj hjn
  · push Not at hS
    refine ⟨0, fun _ => v, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i _; exact ⟨le_rfl, hvn⟩
    · intro i hi; omega
    · intro i hi; omega
    · intro i hi; omega
    · intro i hi; omega
    · intro j hj hjn
      have hxj : x j = x v := le_antisymm (hS j hj hjn) (hx hj.le)
      exact ⟨hxj, hgood j hj hjn hxj⟩

end P172H



/-! Weak-order version of lemma_4_1 (172ae934 stage_step, piece WL41): generators may be
parallel (equal ratios) and horizontal (b = 0), provided horizontal ones are ordered
nonnegative-first. Copied from scratch/probe/a818ff14.lean with GenOrdered -> WOrd. -/

namespace P172W

open AffinePolicyOpt.OneDim Set

variable {k : ℕ}

/-- Weak generator order: `b ≥ 0`, ratios weakly decreasing (cross-multiplied), and among
horizontal generators no negative one precedes a positive one. -/
def WOrd {k : ℕ} (a b : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧ (∀ i j, i < j → a j * b i ≤ a i * b j) ∧
  (∀ i j, i < j → b i = 0 → b j = 0 → a j ≤ 0 ∨ 0 ≤ a i)

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

lemma support_line (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : WOrd a b) (j : ℕ) (hj : j < k)
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
      have hord := hab.2.1 i ⟨j, hj⟩ hij
      have hp : prefixVertex k j i = 1 := by unfold prefixVertex; simp [h]
      rw [hp]
      nlinarith [hwi.2]
    · have : i = ⟨j, hj⟩ := Fin.ext h
      subst this
      have e : b ⟨j, hj⟩ * a ⟨j, hj⟩ - a ⟨j, hj⟩ * b ⟨j, hj⟩ = 0 := by ring
      rw [e, zero_mul]
    · have hij : (⟨j, hj⟩ : Fin k) < i := h
      have hord := hab.2.1 ⟨j, hj⟩ i hij
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


lemma dominated (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : WOrd a b) (f : ℝ → ℝ)
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

lemma caseB (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : WOrd a b) (f : ℝ → ℝ)
    (w : Fin k → ℝ) (hw : w ∈ cube k) (hz : ∀ i, b i = 0) :
    ∃ n ≤ k, (zon a0 b0 a b w).1 + f (zon a0 b0 a b w).2 ≤
      (zon a0 b0 a b (prefixVertex k n)).1 + f (zon a0 b0 a b (prefixVertex k n)).2 := by
  classical
  have h2 : ∀ v, (zon a0 b0 a b v).2 = b0 := by intro v; simp [zon, hz]
  simp only [h2]
  suffices hs : ∃ n ≤ k, ∀ i, a i * w i ≤ a i * prefixVertex k n i by
    obtain ⟨n, hn, h⟩ := hs
    refine ⟨n, hn, ?_⟩
    simp only [zon]
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    linarith
  by_cases hP : ∃ i, 0 < a i
  · set P := Finset.univ.filter (fun i => 0 < a i) with hPdef
    have hPne : P.Nonempty := by obtain ⟨i, hi⟩ := hP; exact ⟨i, by simp [hPdef, hi]⟩
    set p := P.max' hPne with hpdef
    have hpP : 0 < a p := (Finset.mem_filter.1 (P.max'_mem hPne)).2
    refine ⟨(p : ℕ) + 1, p.2, fun i => ?_⟩
    unfold prefixVertex
    by_cases hi : (i : ℕ) < p + 1
    · rw [if_pos hi]
      have hai : 0 ≤ a i := by
        rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with h | h
        · rcases hab.2.2 i p (show i < p from h) (hz i) (hz p) with h' | h'
          · linarith
          · exact h'
        · rw [Fin.ext h]; exact hpP.le
      nlinarith [(hw i).2]
    · rw [if_neg hi]
      have hna : ¬ 0 < a i := fun h => by
        have h3 : i ≤ p := P.le_max' i (by simp [hPdef, h])
        have h4 : (i : ℕ) ≤ p := h3
        omega
      push Not at hna
      nlinarith [(hw i).1]
  · push Not at hP
    refine ⟨0, Nat.zero_le _, fun i => ?_⟩
    simp only [prefixVertex, Nat.not_lt_zero, if_false, mul_zero]
    nlinarith [hP i, (hw i).1]

theorem lemma_4_1w (k : ℕ) (a0 b0 : ℝ) (a b : Fin k → ℝ) (hab : WOrd a b)
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

end P172W



/-! 172ae934 stage_step, piece NC-q (normalized q-step), part 1: block lemmas.
Sequences are ℕ-indexed. Generator `l` is `(a l, b l)`, the matched policy increment is `δ l`
(`-b l ≤ δ l ≤ 0`), and inside a hull block `[p, r)` of slope `K` the terms
`τ l = (a l + c δ l) - K (b l + δ l)` have nonpositive partial sums from `p` and total `0`.
Then every generator of the block admits an aligned policy coefficient `qf` in `[-b, 0]`. -/

namespace P172Q

open Finset

/-- Weak order of generators `l < n` (ℕ-indexed version of `WOrd`). -/
def WOrdN (n : ℕ) (a b : ℕ → ℝ) : Prop :=
  (∀ i, i < n → 0 ≤ b i) ∧ (∀ i j, i < j → j < n → a j * b i ≤ a i * b j) ∧
  (∀ i j, i < j → j < n → b i = 0 → b j = 0 → a j ≤ 0 ∨ 0 ≤ a i)

lemma ml1 {n : ℕ} {a b : ℕ → ℝ} (h : WOrdN n a b) (κ : ℝ) {i : ℕ} (hi : i < n)
    (hai : κ * b i < a i) : ∀ l, l ≤ i → κ * b l ≤ a l := by
  intro l hl
  rcases hl.lt_or_eq with hl | rfl
  · have hbl := h.1 l (by omega)
    have hbi := h.1 i hi
    have hc := h.2.1 l i hl hi
    rcases hbi.lt_or_eq with hbi' | hbi'
    · nlinarith
    · -- b i = 0, so a i > 0, so b l = 0 and a l ≥ 0
      rw [← hbi'] at hai hc
      have hbl0 : b l = 0 := by
        rcases hbl.lt_or_eq with h1 | h1
        · nlinarith
        · exact h1.symm
      rcases h.2.2 l i hl hi hbl0 hbi'.symm with h2 | h2
      · linarith
      · rw [hbl0]; linarith
  · exact hai.le

lemma ml2 {n : ℕ} {a b : ℕ → ℝ} (h : WOrdN n a b) (κ : ℝ) {i : ℕ}
    (hai : a i < κ * b i) : ∀ l, i ≤ l → l < n → a l ≤ κ * b l := by
  intro l hl hln
  rcases hl.lt_or_eq with hl | rfl
  · have hbl := h.1 l hln
    have hbi := h.1 i (by omega)
    have hc := h.2.1 i l hl hln
    rcases hbi.lt_or_eq with hbi' | hbi'
    · nlinarith
    · rw [← hbi'] at hai hc
      have hbl0 : b l = 0 := by
        rcases hbl.lt_or_eq with h1 | h1
        · nlinarith
        · exact h1.symm
      rcases h.2.2 i l hl hln hbi'.symm hbl0 with h2 | h2
      · rw [hbl0]; linarith
      · linarith
  · exact hai.le

/-- The block lemma: in a hull block every generator lies between slope `K` and `c`. -/
lemma block_between {n : ℕ} {a b δ : ℕ → ℝ} (h : WOrdN n a b) (c K : ℝ)
    (hδ : ∀ l, l < n → -b l ≤ δ l ∧ δ l ≤ 0) {p r : ℕ} (hpr : p < r) (hrn : r ≤ n)
    (hbel : ∀ j, p < j → j < r →
      ∑ l ∈ Ico p j, ((a l + c * δ l) - K * (b l + δ l)) ≤ 0)
    (hend : ∑ l ∈ Ico p r, ((a l + c * δ l) - K * (b l + δ l)) = 0)
    (i : ℕ) (hpi : p ≤ i) (hir : i < r) :
    (K < c → K * b i ≤ a i ∧ a i ≤ c * b i) ∧ (c < K → c * b i ≤ a i ∧ a i ≤ K * b i) ∧
      (K = c → a i = c * b i) := by
  set τ : ℕ → ℝ := fun l => (a l + c * δ l) - K * (b l + δ l) with hτ
  have hin : i < n := by omega
  -- prefix through i is ≤ 0
  have hpre : ∑ l ∈ Ico p (i + 1), τ l ≤ 0 := by
    rcases (show i + 1 ≤ r by omega).lt_or_eq with h1 | h1
    · exact hbel (i + 1) (by omega) h1
    · rw [h1]; exact hend.le
  -- suffix from i is ≥ 0
  have hsuf : 0 ≤ ∑ l ∈ Ico i r, τ l := by
    have hsplit := Finset.sum_Ico_consecutive τ hpi hir.le
    rcases hpi.lt_or_eq with h1 | h1
    · have := hbel i h1 hir
      linarith
    · subst h1; linarith
  -- prefix positivity from a strict term at i with nonneg terms before
  have pre_pos : ∀ (f : ℕ → ℝ), (∀ l, p ≤ l → l ≤ i → f l ≤ τ l) → (∀ l, p ≤ l → l ≤ i → 0 ≤ f l) →
      0 < f i → False := by
    intro f hfτ hf0 hfi
    have h1 : ∑ l ∈ Ico p (i + 1), f l ≤ ∑ l ∈ Ico p (i + 1), τ l :=
      Finset.sum_le_sum (fun l hl => by
        rw [Finset.mem_Ico] at hl; exact hfτ l hl.1 (by omega))
    have h2 : 0 < ∑ l ∈ Ico p (i + 1), f l := by
      apply Finset.sum_pos' (fun l hl => by rw [Finset.mem_Ico] at hl; exact hf0 l hl.1 (by omega))
      exact ⟨i, Finset.mem_Ico.2 ⟨hpi, by omega⟩, hfi⟩
    linarith
  have suf_neg : ∀ (f : ℕ → ℝ), (∀ l, i ≤ l → l < r → τ l ≤ f l) → (∀ l, i ≤ l → l < r → f l ≤ 0) →
      f i < 0 → False := by
    intro f hfτ hf0 hfi
    have h1 : ∑ l ∈ Ico i r, τ l ≤ ∑ l ∈ Ico i r, f l :=
      Finset.sum_le_sum (fun l hl => by rw [Finset.mem_Ico] at hl; exact hfτ l hl.1 hl.2)
    have h2 : ∑ l ∈ Ico i r, f l < 0 := by
      apply Finset.sum_neg' (fun l hl => by rw [Finset.mem_Ico] at hl; exact hf0 l hl.1 hl.2)
      exact ⟨i, Finset.mem_Ico.2 ⟨le_rfl, hir⟩, hfi⟩
    linarith
  refine ⟨fun hK => ⟨?_, ?_⟩, fun hK => ⟨?_, ?_⟩, fun hK => ?_⟩
  · by_contra hc; push Not at hc
    have hm := ml2 h K hc
    exact suf_neg (fun l => a l - K * b l)
      (fun l hl1 hl2 => by
        have := (hδ l (by omega)).2
        simp only [hτ]; nlinarith)
      (fun l hl1 hl2 => by have := hm l hl1 (by omega); linarith) (by linarith)
  · by_contra hc; push Not at hc
    have hm := ml1 h c hin hc
    exact pre_pos (fun l => a l - c * b l)
      (fun l hl1 hl2 => by
        have := (hδ l (by omega)).1
        simp only [hτ]; nlinarith)
      (fun l hl1 hl2 => by have := hm l hl2; linarith) (by linarith)
  · by_contra hc; push Not at hc
    have hm := ml2 h c hc
    exact suf_neg (fun l => a l - c * b l)
      (fun l hl1 hl2 => by
        have := (hδ l (by omega)).1
        simp only [hτ]; nlinarith)
      (fun l hl1 hl2 => by have := hm l hl1 (by omega); linarith) (by linarith)
  · by_contra hc; push Not at hc
    have hm := ml1 h K hin hc
    exact pre_pos (fun l => a l - K * b l)
      (fun l hl1 hl2 => by
        have := (hδ l (by omega)).2
        simp only [hτ]; nlinarith)
      (fun l hl1 hl2 => by have := hm l hl2; linarith) (by linarith)
  · subst hK
    rcases lt_trichotomy (a i) (K * b i) with hc | hc | hc
    · exfalso
      have hm := ml2 h K hc
      exact suf_neg (fun l => a l - K * b l)
        (fun l hl1 hl2 => by simp only [hτ]; nlinarith)
        (fun l hl1 hl2 => by have := hm l hl1 (by omega); linarith) (by linarith)
    · exact hc
    · exfalso
      have hm := ml1 h K hin hc
      exact pre_pos (fun l => a l - K * b l)
        (fun l hl1 hl2 => by simp only [hτ]; nlinarith)
        (fun l hl1 hl2 => by have := hm l hl2; linarith) (by linarith)

/-- The aligned policy coefficient of generator `i` in a block of slope `K`. -/
noncomputable def qf (a b δ : ℕ → ℝ) (c K : ℝ) (i : ℕ) : ℝ :=
  if K = c then δ i else (K * b i - a i) / (c - K)

lemma qf_props (a b δ : ℕ → ℝ) (c K : ℝ) (i : ℕ) (hδ : -b i ≤ δ i ∧ δ i ≤ 0)
    (hB : (K < c → K * b i ≤ a i ∧ a i ≤ c * b i) ∧ (c < K → c * b i ≤ a i ∧ a i ≤ K * b i) ∧
      (K = c → a i = c * b i)) :
    (-b i ≤ qf a b δ c K i ∧ qf a b δ c K i ≤ 0) ∧
      a i + c * qf a b δ c K i = K * (b i + qf a b δ c K i) := by
  unfold qf
  rcases lt_trichotomy K c with hK | hK | hK
  · have hne : K ≠ c := ne_of_lt hK
    rw [if_neg hne]
    obtain ⟨h1, h2⟩ := hB.1 hK
    have hpos : 0 < c - K := sub_pos.2 hK
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hpos]; nlinarith
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    · field_simp; ring
  · subst hK
    rw [if_pos rfl]
    exact ⟨hδ, by rw [hB.2.2 rfl]; ring⟩
  · have hne : K ≠ c := ne_of_gt hK
    rw [if_neg hne]
    obtain ⟨h1, h2⟩ := hB.2.1 hK
    have hneg : c - K < 0 := sub_neg.2 hK
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff_of_neg hneg]; nlinarith
    · exact div_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le
    · have : c - K ≠ 0 := ne_of_lt hneg
      field_simp; ring

lemma qf_block_sum (a b δ : ℕ → ℝ) (c K : ℝ) (p r : ℕ)
    (hend : ∑ l ∈ Ico p r, ((a l + c * δ l) - K * (b l + δ l)) = 0) :
    ∑ l ∈ Ico p r, qf a b δ c K l = ∑ l ∈ Ico p r, δ l := by
  unfold qf
  by_cases hK : K = c
  · simp [hK]
  · simp only [hK, if_false]
    rw [← Finset.sum_div]
    have hne : c - K ≠ 0 := sub_ne_zero.2 (Ne.symm hK)
    rw [div_eq_iff hne]
    have e1 : ∑ l ∈ Ico p r, ((a l + c * δ l) - K * (b l + δ l)) =
        ∑ l ∈ Ico p r, a l + c * ∑ l ∈ Ico p r, δ l - K * ∑ l ∈ Ico p r, b l -
          K * ∑ l ∈ Ico p r, δ l := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
      ring
    have e2 : ∑ l ∈ Ico p r, (K * b l - a l) = K * ∑ l ∈ Ico p r, b l - ∑ l ∈ Ico p r, a l := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e2]
    linarith

end P172Q

namespace P172Q

open Finset P172H

/-- Old matched chain points: state coordinate `Yp` and cost coordinate `Gp` (without base). -/
noncomputable def Yp (b δ : ℕ → ℝ) (j : ℕ) : ℝ := ∑ l ∈ range j, (b l + δ l)
noncomputable def Gp (a δ : ℕ → ℝ) (c : ℝ) (j : ℕ) : ℝ := ∑ l ∈ range j, (a l + c * δ l)

lemma Yp_mono {n : ℕ} {b δ : ℕ → ℝ} (hδ : ∀ l, l < n → -b l ≤ δ l ∧ δ l ≤ 0) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) : Yp b δ i ≤ Yp b δ j := by
  unfold Yp
  rw [← Finset.sum_range_add_sum_Ico _ hij]
  have : 0 ≤ ∑ l ∈ Ico i j, (b l + δ l) := Finset.sum_nonneg (fun l hl => by
    rw [mem_Ico] at hl; have := hδ l (by omega); linarith)
  linarith

lemma zero_prog {n : ℕ} {b δ : ℕ → ℝ} (hδ : ∀ l, l < n → -b l ≤ δ l ∧ δ l ≤ 0) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) (he : Yp b δ i = Yp b δ j) :
    ∀ l, i ≤ l → l < j → b l + δ l = 0 := by
  intro l hl1 hl2
  have hsum : ∑ l ∈ Ico i j, (b l + δ l) = 0 := by
    have := Finset.sum_range_add_sum_Ico (fun l => b l + δ l) hij
    unfold Yp at he
    linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun l hl => by
    rw [mem_Ico] at hl; have := hδ l (by omega); linarith)).1 hsum l (mem_Ico.2 ⟨hl1, hl2⟩)

lemma lead_top {n : ℕ} {a b δ : ℕ → ℝ} {c : ℝ} (h : WOrdN n a b)
    (hδ : ∀ l, l < n → -b l ≤ δ l ∧ δ l ≤ 0) :
    ∃ v0 ≤ n, (∀ l, l < v0 → b l + δ l = 0 ∧ 0 ≤ a l + c * δ l) ∧
      (∀ j, v0 < j → j ≤ n → Yp b δ j = Yp b δ v0 → Gp a δ c j ≤ Gp a δ c v0) := by
  classical
  set C := (range (n + 1)).filter (fun j => Yp b δ j = Yp b δ 0) with hCdef
  have hC0 : 0 ∈ C := by simp [hCdef]
  obtain ⟨j0, hj0C, hmax⟩ := C.exists_max_image (Gp a δ c) ⟨0, hC0⟩
  set Tset := C.filter (fun j => Gp a δ c j = Gp a δ c j0) with hTdef
  have hTne : Tset.Nonempty := ⟨j0, mem_filter.2 ⟨hj0C, rfl⟩⟩
  set v0 := Tset.max' hTne with hv0
  have hvT := Tset.max'_mem hTne
  have hvC : v0 ∈ C := (mem_filter.1 hvT).1
  have hvG : Gp a δ c v0 = Gp a δ c j0 := (mem_filter.1 hvT).2
  have hvn : v0 ≤ n := by
    have := (mem_filter.1 hvC).1; rw [mem_range] at this; omega
  have hvY : Yp b δ v0 = Yp b δ 0 := (mem_filter.1 hvC).2
  have hz : ∀ l, l < v0 → b l + δ l = 0 :=
    fun l hl => zero_prog hδ (Nat.zero_le _) hvn hvY.symm l (Nat.zero_le _) hl
  have hY0 : Yp b δ 0 = 0 := by simp [Yp]
  refine ⟨v0, hvn, fun l hl => ⟨hz l hl, ?_⟩, ?_⟩
  · by_contra hneg
    push Not at hneg
    have hdl : δ l = -b l := by have := hz l hl; linarith
    have hm := ml2 h c (show a l < c * b l by rw [hdl] at hneg; linarith)
    have hle : ∀ l', l < l' → l' < v0 → a l' + c * δ l' ≤ 0 := by
      intro l' h1 h2
      have := hm l' h1.le (by omega)
      have : δ l' = -b l' := by have := hz l' h2; linarith
      rw [this]; linarith
    have hlC : l ∈ C := by
      rw [hCdef, mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      rw [hY0]; unfold Yp
      exact Finset.sum_eq_zero (fun i hi => hz i (by rw [mem_range] at hi; omega))
    have h1 := hmax l hlC
    have h2 : Gp a δ c v0 - Gp a δ c l ≤ a l + c * δ l := by
      unfold Gp
      rw [← Finset.sum_range_add_sum_Ico _ hl.le, Finset.sum_eq_sum_Ico_succ_bot hl]
      have : ∑ i ∈ Ico (l + 1) v0, (a i + c * δ i) ≤ 0 := Finset.sum_nonpos (fun i hi => by
        rw [mem_Ico] at hi; exact hle i (by omega) hi.2)
      linarith
    linarith
  · intro j hj hjn hjY
    have hjC : j ∈ C := by
      rw [hCdef, mem_filter, mem_range]; exact ⟨by omega, hjY.trans hvY⟩
    rw [hvG]; exact hmax j hjC

/-- Main normalized q-step: aligned policy coefficients exist. -/
theorem ncq_main (n : ℕ) (a b δ : ℕ → ℝ) (c : ℝ) (h : WOrdN n a b)
    (hδ : ∀ l, l < n → -b l ≤ δ l ∧ δ l ≤ 0) :
    ∃ q : ℕ → ℝ, (∀ l, l < n → -b l ≤ q l ∧ q l ≤ 0) ∧
      ∑ l ∈ range n, q l = ∑ l ∈ range n, δ l ∧
      WOrdN n (fun l => a l + c * q l) (fun l => b l + q l) ∧
      ∀ j, j ≤ n → ∃ j1, j1 ≤ n ∧ ∃ j2, j2 ≤ n ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
        ∑ l ∈ range j, (a l + c * q l) = (1 - μ) * Gp a δ c j1 + μ * Gp a δ c j2 ∧
        ∑ l ∈ range j, (b l + q l) = (1 - μ) * Yp b δ j1 + μ * Yp b δ j2 := by
  classical
  obtain ⟨v0, hv0n, hlead, htop⟩ := lead_top (c := c) h hδ
  set x : ℕ → ℝ := fun j => Yp b δ (min j n) with hxdef
  set y : ℕ → ℝ := fun j => Gp a δ c (min j n) with hydef
  have hxj : ∀ j, j ≤ n → x j = Yp b δ j := fun j hj => by simp [hxdef, min_eq_left hj]
  have hyj : ∀ j, j ≤ n → y j = Gp a δ c j := fun j hj => by simp [hydef, min_eq_left hj]
  have hxmono : Monotone x := by
    intro i j hij
    exact Yp_mono hδ (min_le_min_right n hij) (min_le_right _ _)
  obtain ⟨m, s, hH⟩ := hull_exists x y hxmono n (n - v0) v0 rfl hv0n (fun j hj hjn hxe => by
    rw [hxj j hjn, hxj v0 hv0n] at hxe
    rw [hyj j hjn, hyj v0 hv0n]
    exact htop j hj hjn hxe)
  obtain ⟨hs0, hrng, hinc, hxinc, hanti, hbel, hlast⟩ := hH
  set e := s m with he
  have hen : e ≤ n := (hrng m le_rfl).2
  have hve : v0 ≤ e := (hrng m le_rfl).1
  -- strict monotonicity of the hull vertices
  have smono : ∀ i j, i < j → j ≤ m → s i < s j := by
    intro i j hij hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases (Nat.lt_succ_iff.1 hij).lt_or_eq with h1 | h1
      · exact lt_trans (ih h1 (by omega)) (hinc j (by omega))
      · subst h1; exact hinc i (by omega)
  have smono' : ∀ i j, i ≤ j → j ≤ m → s i ≤ s j := by
    intro i j hij hjm
    rcases hij.lt_or_eq with h1 | h1
    · exact (smono i j h1 hjm).le
    · rw [h1]
  -- trailing part
  have htrail : ∀ l, e ≤ l → l < n → b l + δ l = 0 ∧ a l + c * δ l ≤ 0 := by
    have hYe : Yp b δ e = Yp b δ n := by
      rcases hen.lt_or_eq with h1 | h1
      · have := (hlast n h1 le_rfl).1
        rw [hxj n le_rfl, hxj e hen] at this
        exact this.symm
      · rw [h1]
    have hz : ∀ l, e ≤ l → l < n → b l + δ l = 0 := zero_prog hδ hen le_rfl hYe
    intro l hl1 hl2
    refine ⟨hz l hl1 hl2, ?_⟩
    by_contra hpos
    push Not at hpos
    have hnn : ∀ l', e ≤ l' → l' < l → 0 ≤ a l' + c * δ l' := by
      intro l' h1 h2
      by_contra hneg
      push Not at hneg
      have hdl : δ l' = -b l' := by have := hz l' h1 (by omega); linarith
      have hm := ml2 h c (show a l' < c * b l' by rw [hdl] at hneg; linarith)
      have := hm l h2.le hl2
      have hdl2 : δ l = -b l := by have := hz l hl1 hl2; linarith
      rw [hdl2] at hpos
      linarith
    have hlt := (hlast (l + 1) (by omega) (by omega)).2
    rw [hyj (l + 1) (by omega), hyj e hen] at hlt
    have : Gp a δ c (l + 1) - Gp a δ c e ≥ a l + c * δ l := by
      unfold Gp
      rw [← Finset.sum_range_add_sum_Ico _ (show e ≤ l + 1 by omega), Finset.sum_Ico_succ_top hl1]
      have : 0 ≤ ∑ i ∈ Ico e l, (a i + c * δ i) := Finset.sum_nonneg (fun i hi => by
        rw [mem_Ico] at hi; exact hnn i hi.1 hi.2)
      linarith
    linarith
  -- slopes and their antitonicity
  set K : ℕ → ℝ := fun i => sl x y (s i) (s (i + 1)) with hKdef
  have kanti : ∀ i j, i ≤ j → j < m → K j ≤ K i := by
    intro i j hij hjm
    induction j with
    | zero => rw [Nat.le_zero.1 hij]
    | succ j ih =>
      rcases hij.lt_or_eq with h1 | h1
      · exact le_trans (hanti j (by omega)) (ih (by omega) (by omega))
      · rw [h1]
  -- block index
  set bi : ℕ → ℕ := fun l => Nat.findGreatest (fun i => s i ≤ l) m with hbidef
  have bi_spec : ∀ l, v0 ≤ l → l < e → bi l < m ∧ s (bi l) ≤ l ∧ l < s (bi l + 1) := by
    intro l hl1 hl2
    have hP0 : s 0 ≤ l := by rw [hs0]; exact hl1
    have hspec : s (bi l) ≤ l := Nat.findGreatest_spec (P := fun i => s i ≤ l) (Nat.zero_le m) hP0
    have hle : bi l ≤ m := Nat.findGreatest_le m
    have hlt : bi l < m := by
      rcases hle.lt_or_eq with h1 | h1
      · exact h1
      · exfalso; rw [h1] at hspec; omega
    refine ⟨hlt, hspec, ?_⟩
    by_contra hc
    push Not at hc
    exact Nat.findGreatest_is_greatest (P := fun i => s i ≤ l) (Nat.lt_succ_self (bi l))
      (by omega) hc
  have bi_eq : ∀ i, i < m → ∀ l, s i ≤ l → l < s (i + 1) → bi l = i := by
    intro i hi l hl1 hl2
    have h1 : i ≤ bi l := Nat.le_findGreatest (P := fun i => s i ≤ l) hi.le hl1
    have hv : v0 ≤ l := by rw [← hs0]; exact le_trans (smono' 0 i (Nat.zero_le _) hi.le) hl1
    have he' : l < e := lt_of_lt_of_le hl2 (smono' (i + 1) m (by omega) le_rfl)
    obtain ⟨_, hsp, _⟩ := bi_spec l hv he'
    by_contra hne
    have h2 : i + 1 ≤ bi l := by omega
    have := smono' (i + 1) (bi l) h2 (Nat.findGreatest_le m)
    omega
  have bi_mono : ∀ l l', l ≤ l' → bi l ≤ bi l' := by
    intro l l' hll
    exact Nat.findGreatest_mono_left (fun i (hi : s i ≤ l) => le_trans hi hll) m
  -- block data in Yp/Gp form
  have blk : ∀ i, i < m →
      Yp b δ (s i) < Yp b δ (s (i + 1)) ∧
      (∀ j, s i < j → j < s (i + 1) →
        ∑ l ∈ Ico (s i) j, ((a l + c * δ l) - K i * (b l + δ l)) ≤ 0) ∧
      ∑ l ∈ Ico (s i) (s (i + 1)), ((a l + c * δ l) - K i * (b l + δ l)) = 0 := by
    intro i hi
    have hsi : s i ≤ n := (hrng i hi.le).2
    have hsi1 : s (i + 1) ≤ n := (hrng (i + 1) hi).2
    have hx := hxinc i hi
    rw [hxj _ hsi, hxj _ hsi1] at hx
    have hsplit : ∀ j, s i ≤ j → j ≤ n →
        ∑ l ∈ Ico (s i) j, ((a l + c * δ l) - K i * (b l + δ l)) =
          (Gp a δ c j - Gp a δ c (s i)) - K i * (Yp b δ j - Yp b δ (s i)) := by
      intro j hj1 hj2
      unfold Gp Yp
      rw [← Finset.sum_range_add_sum_Ico (fun l => a l + c * δ l) hj1,
        ← Finset.sum_range_add_sum_Ico (fun l => b l + δ l) hj1,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    refine ⟨hx, fun j hj1 hj2 => ?_, ?_⟩
    · have hjn : j ≤ n := by omega
      rw [hsplit j hj1.le hjn]
      have := hbel i hi j hj1 hj2
      rw [hxj j hjn, hxj _ hsi, hyj j hjn, hyj _ hsi] at this
      linarith
    · rw [hsplit _ (hinc i hi).le hsi1]
      have := sl_spec x y (s i) (s (i + 1)) (hxinc i hi)
      rw [hxj _ hsi, hxj _ hsi1, hyj _ hsi, hyj _ hsi1] at this
      have hK : K i = sl x y (s i) (s (i + 1)) := rfl
      rw [hK]; linarith
  -- the policy coefficients
  set q : ℕ → ℝ := fun l => if l < v0 then δ l else if l < e then qf a b δ c (K (bi l)) l else δ l
    with hqdef
  have q_blk : ∀ i, i < m → ∀ l, s i ≤ l → l < s (i + 1) → q l = qf a b δ c (K i) l := by
    intro i hi l hl1 hl2
    have hv : v0 ≤ l := by rw [← hs0]; exact le_trans (smono' 0 i (Nat.zero_le _) hi.le) hl1
    have he' : l < e := lt_of_lt_of_le hl2 (smono' (i + 1) m (by omega) le_rfl)
    simp only [hqdef, show ¬ l < v0 by omega, if_false, he', if_true, bi_eq i hi l hl1 hl2]
  have blk_between : ∀ i, i < m → ∀ l, s i ≤ l → l < s (i + 1) →
      (-b l ≤ q l ∧ q l ≤ 0) ∧ a l + c * q l = K i * (b l + q l) := by
    intro i hi l hl1 hl2
    obtain ⟨hY, hb, hend⟩ := blk i hi
    have hsi1 : s (i + 1) ≤ n := (hrng (i + 1) hi).2
    have hB := block_between h c (K i) hδ (hinc i hi) hsi1 hb hend l hl1 hl2
    rw [q_blk i hi l hl1 hl2]
    exact qf_props a b δ c (K i) l (hδ l (by omega)) hB
  -- region facts
  have hregion : ∀ l, l < n →
      (l < v0 ∧ q l = δ l) ∨ (v0 ≤ l ∧ l < e ∧ s (bi l) ≤ l ∧ l < s (bi l + 1) ∧ bi l < m) ∨
        (e ≤ l ∧ q l = δ l) := by
    intro l hl
    by_cases h1 : l < v0
    · left; exact ⟨h1, by simp [hqdef, h1]⟩
    · by_cases h2 : l < e
      · right; left
        obtain ⟨a1, a2, a3⟩ := bi_spec l (by omega) h2
        exact ⟨by omega, h2, a2, a3, a1⟩
      · right; right; exact ⟨by omega, by simp [hqdef, h1, h2]⟩
  have q_bounds : ∀ l, l < n → -b l ≤ q l ∧ q l ≤ 0 := by
    intro l hl
    rcases hregion l hl with ⟨_, hq⟩ | ⟨_, _, h3, h4, h5⟩ | ⟨_, hq⟩
    · rw [hq]; exact hδ l hl
    · exact (blk_between (bi l) h5 l h3 h4).1
    · rw [hq]; exact hδ l hl
  -- matching at hull vertices
  have match_s : ∀ i, i ≤ m → ∑ l ∈ range (s i), q l = ∑ l ∈ range (s i), δ l := by
    intro i hi
    induction i with
    | zero =>
      rw [hs0]
      exact Finset.sum_congr rfl (fun l hl => by
        rw [mem_range] at hl; simp [hqdef, hl])
    | succ i ih =>
      have hle := (hinc i (by omega)).le
      rw [← Finset.sum_range_add_sum_Ico _ hle, ← Finset.sum_range_add_sum_Ico δ hle,
        ih (by omega)]
      have hb : ∑ l ∈ Ico (s i) (s (i + 1)), q l = ∑ l ∈ Ico (s i) (s (i + 1)), qf a b δ c (K i) l :=
        Finset.sum_congr rfl (fun l hl => by
          rw [mem_Ico] at hl; exact q_blk i (by omega) l hl.1 hl.2)
      rw [hb, qf_block_sum a b δ c (K i) _ _ (blk i (by omega)).2.2]
  have match_lead : ∀ j, j ≤ v0 → ∑ l ∈ range j, q l = ∑ l ∈ range j, δ l := by
    intro j hj
    exact Finset.sum_congr rfl (fun l hl => by
      rw [mem_range] at hl; simp [hqdef, show l < v0 by omega])
  have match_trail : ∀ j, e ≤ j → j ≤ n → ∑ l ∈ range j, q l = ∑ l ∈ range j, δ l := by
    intro j hj1 hj2
    rw [← Finset.sum_range_add_sum_Ico _ hj1, ← Finset.sum_range_add_sum_Ico δ hj1,
      match_s m le_rfl]
    congr 1
    exact Finset.sum_congr rfl (fun l hl => by
      rw [mem_Ico] at hl
      simp [hqdef, show ¬ l < v0 by omega, show ¬ l < e by omega])
  -- new generator shapes
  have gen_lead : ∀ l, l < v0 → b l + q l = 0 ∧ 0 ≤ a l + c * q l := by
    intro l hl
    have hq : q l = δ l := by simp [hqdef, hl]
    rw [hq]; exact hlead l hl
  have gen_trail : ∀ l, e ≤ l → l < n → b l + q l = 0 ∧ a l + c * q l ≤ 0 := by
    intro l hl1 hl2
    have hq : q l = δ l := by simp [hqdef, show ¬ l < v0 by omega, show ¬ l < e by omega]
    rw [hq]; exact htrail l hl1 hl2
  have gen_blk : ∀ l, v0 ≤ l → l < e → 0 ≤ b l + q l ∧ a l + c * q l = K (bi l) * (b l + q l) := by
    intro l hl1 hl2
    obtain ⟨h1, h2, h3⟩ := bi_spec l hl1 hl2
    obtain ⟨⟨hq1, _⟩, hal⟩ := blk_between (bi l) h1 l h2 h3
    exact ⟨by linarith, hal⟩
  refine ⟨q, q_bounds, ?_, ?_, ?_⟩
  · -- total matching
    rcases hen.lt_or_eq with h1 | h1
    · exact match_trail n h1.le le_rfl
    · rw [← h1]; exact match_s m le_rfl
  · -- weak order of the new generators
    refine ⟨fun l hl => by have := q_bounds l hl; linarith, ?_, ?_⟩
    · intro i j hij hjn
      show (a j + c * q j) * (b i + q i) ≤ (a i + c * q i) * (b j + q j)
      by_cases hi : i < v0
      · obtain ⟨h1, h2⟩ := gen_lead i hi
        rw [h1]
        have := q_bounds j hjn
        nlinarith
      · by_cases hj : e ≤ j
        · obtain ⟨h1, h2⟩ := gen_trail j hj hjn
          rw [h1]
          have := q_bounds i (by omega)
          nlinarith
        · obtain ⟨hbi, hai⟩ := gen_blk i (by omega) (by omega)
          obtain ⟨hbj, haj⟩ := gen_blk j (by omega) (by omega)
          rw [hai, haj]
          have hK : K (bi j) ≤ K (bi i) :=
            kanti (bi i) (bi j) (bi_mono i j hij.le) (bi_spec j (by omega) (by omega)).1
          have := mul_nonneg hbi hbj
          nlinarith
    · intro i j hij hjn hbi0 hbj0
      have hbi0' : b i + q i = 0 := hbi0
      show a j + c * q j ≤ 0 ∨ 0 ≤ a i + c * q i
      by_cases hi : i < v0
      · right; exact (gen_lead i hi).2
      · by_cases hj : e ≤ j
        · left; exact (gen_trail j hj hjn).2
        · right
          have := (gen_blk i (by omega) (by omega)).2
          rw [this, hbi0', mul_zero]
  · -- every new prefix point is a convex combination of two old matched points
    intro j hjn
    have hsumA : ∀ j', ∑ l ∈ range j', (a l + c * q l) =
        Gp a δ c j' + c * (∑ l ∈ range j', q l - ∑ l ∈ range j', δ l) := by
      intro j'; unfold Gp
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    have hsumB : ∀ j', ∑ l ∈ range j', (b l + q l) =
        Yp b δ j' + (∑ l ∈ range j', q l - ∑ l ∈ range j', δ l) := by
      intro j'; unfold Yp
      simp only [Finset.sum_add_distrib]; ring
    have matched : ∀ j', j' ≤ n → ∑ l ∈ range j', q l = ∑ l ∈ range j', δ l →
        ∃ j1, j1 ≤ n ∧ ∃ j2, j2 ≤ n ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
          ∑ l ∈ range j', (a l + c * q l) = (1 - μ) * Gp a δ c j1 + μ * Gp a δ c j2 ∧
          ∑ l ∈ range j', (b l + q l) = (1 - μ) * Yp b δ j1 + μ * Yp b δ j2 := by
      intro j' hj' hm
      refine ⟨j', hj', j', hj', 0, le_rfl, zero_le_one, ?_, ?_⟩
      · rw [hsumA, hm]; ring
      · rw [hsumB, hm]; ring
    by_cases h1 : j ≤ v0
    · exact matched j hjn (match_lead j h1)
    · by_cases h2 : e ≤ j
      · exact matched j hjn (match_trail j h2 hjn)
      · -- j strictly inside the hull range: block i = bi j
        obtain ⟨hi, hsj, hjs⟩ := bi_spec j (by omega) (by omega)
        set i := bi j
        set p := s i
        set r := s (i + 1)
        have hrn : r ≤ n := (hrng (i + 1) hi).2
        have hpn : p ≤ n := (hrng i hi.le).2
        obtain ⟨hY, _, hend⟩ := blk i hi
        have hmp := match_s i hi.le
        have hmr := match_s (i + 1) hi
        -- partial sums from p
        have hpartB : ∀ j', p ≤ j' → ∑ l ∈ range j', (b l + q l) =
            Yp b δ p + ∑ l ∈ Ico p j', (b l + q l) := by
          intro j' hj'
          rw [← Finset.sum_range_add_sum_Ico _ hj', hsumB p, hmp, sub_self, add_zero]
        have hpartA : ∀ j', p ≤ j' → j' ≤ r → ∑ l ∈ range j', (a l + c * q l) =
            Gp a δ c p + K i * ∑ l ∈ Ico p j', (b l + q l) := by
          intro j' hj1 hj2
          rw [← Finset.sum_range_add_sum_Ico _ hj1, hsumA p, hmp, sub_self, mul_zero, add_zero,
            Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl (fun l hl => by
            rw [mem_Ico] at hl; exact (blk_between i hi l hl.1 (by omega)).2)
        set S := ∑ l ∈ Ico p j, (b l + q l) with hS
        set D := Yp b δ r - Yp b δ p with hD
        have hDpos : 0 < D := by rw [hD]; linarith
        have hSr : ∑ l ∈ Ico p r, (b l + q l) = D := by
          have := hpartB r (hinc i hi).le
          rw [hsumB r, hmr, sub_self, add_zero] at this
          rw [hD]; linarith
        have hS0 : 0 ≤ S := Finset.sum_nonneg (fun l hl => by
          rw [mem_Ico] at hl; have := q_bounds l (by omega); linarith)
        have hSle : S ≤ D := by
          rw [← hSr, ← Finset.sum_Ico_consecutive _ hsj hjs.le]
          have : 0 ≤ ∑ l ∈ Ico j r, (b l + q l) := Finset.sum_nonneg (fun l hl => by
            rw [mem_Ico] at hl; have := q_bounds l (by omega); linarith)
          linarith
        have hGr : Gp a δ c r - Gp a δ c p = K i * D := by
          have e1 : ∑ l ∈ Ico p r, ((a l + c * δ l) - K i * (b l + δ l)) =
              (Gp a δ c r - Gp a δ c p) - K i * (Yp b δ r - Yp b δ p) := by
            unfold Gp Yp
            rw [← Finset.sum_range_add_sum_Ico (fun l => a l + c * δ l) (hinc i hi).le,
              ← Finset.sum_range_add_sum_Ico (fun l => b l + δ l) (hinc i hi).le,
              Finset.sum_sub_distrib, ← Finset.mul_sum]
            ring
          rw [hD]; linarith
        refine ⟨p, hpn, r, hrn, S / D, div_nonneg hS0 hDpos.le, (div_le_one hDpos).2 hSle, ?_, ?_⟩
        · rw [hpartA j hsj hjs.le]
          have : Gp a δ c r = Gp a δ c p + K i * D := by linarith
          rw [this]
          field_simp
          ring
        · rw [hpartB j hsj]
          have : Yp b δ r = Yp b δ p + D := by rw [hD]; ring
          rw [this]
          field_simp
          ring

end P172Q

namespace P172Z

open Finset P172H P172Q AffinePolicyOpt.OneDim

lemma sum_prefix (m j : ℕ) (hj : j ≤ m) (f : ℕ → ℝ) :
    ∑ i : Fin m, f i * prefixVertex m j i = ∑ l ∈ range j, f l := by
  have e0 : ∑ i : Fin m, f i * prefixVertex m j i =
      ∑ i : Fin m, (fun l : ℕ => f l * (if l < j then (1 : ℝ) else 0)) i := rfl
  rw [e0, Fin.sum_univ_eq_sum_range (fun l : ℕ => f l * (if l < j then (1 : ℝ) else 0)) m,
    ← Finset.sum_range_add_sum_Ico _ hj]
  have h1 : ∑ l ∈ range j, f l * (if l < j then (1 : ℝ) else 0) = ∑ l ∈ range j, f l :=
    Finset.sum_congr rfl (fun l hl => by rw [if_pos (mem_range.1 hl), mul_one])
  have h2 : ∑ l ∈ Ico j m, f l * (if l < j then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero (fun l hl => by
      rw [mem_Ico] at hl; rw [if_neg (by omega), mul_zero])
  rw [h1, h2, add_zero]

/-- ℕ-indexed weak lemma_4_1. -/
lemma wl41n (m : ℕ) (a b : ℕ → ℝ) (h : WOrdN m a b) (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (w : ℕ → ℝ) (hw : ∀ l, l < m → 0 ≤ w l ∧ w l ≤ 1) :
    ∃ j, j ≤ m ∧ ∑ l ∈ range m, a l * w l + f (∑ l ∈ range m, b l * w l) ≤
      ∑ l ∈ range j, a l + f (∑ l ∈ range j, b l) := by
  have hW : P172W.WOrd (fun i : Fin m => a i) (fun i : Fin m => b i) :=
    ⟨fun i => h.1 i i.2, fun i j hij => h.2.1 i j hij j.2, fun i j hij => h.2.2 i j hij j.2⟩
  obtain ⟨j, hj, hmax⟩ := P172W.lemma_4_1w m 0 0 _ _ hW f hf
  have hwc : (fun i : Fin m => w i) ∈ cube m := fun i => ⟨(hw i i.2).1, (hw i i.2).2⟩
  have hle := isMaxOn_iff.1 hmax _ hwc
  simp only [zon, zero_add] at hle
  rw [sum_prefix m j hj a, sum_prefix m j hj b,
    Fin.sum_univ_eq_sum_range (fun l => a l * w l) m,
    Fin.sum_univ_eq_sum_range (fun l => b l * w l) m] at hle
  exact ⟨j, hj, hle⟩

lemma incr_mono {h : ℝ → ℝ} (hh : ConvexOn ℝ Set.univ h) {u v x : ℝ} (hx : 0 ≤ x) (huv : u ≤ v) :
    h (u + x) - h u ≤ h (v + x) - h v := by
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0]; simp
  · have hd : 0 < v + x - u := by linarith
    have hα0 : 0 ≤ x / (v + x - u) := div_nonneg hx hd.le
    have hβ0 : 0 ≤ (v - u) / (v + x - u) := div_nonneg (by linarith) hd.le
    have hsum : (x / (v + x - u)) + ((v - u) / (v + x - u)) = 1 := by
      field_simp; ring
    have hsum' : ((v - u) / (v + x - u)) + (x / (v + x - u)) = 1 := by linarith
    have h1 := hh.2 (Set.mem_univ u) (Set.mem_univ (v + x)) hβ0 hα0 hsum'
    have h2 := hh.2 (Set.mem_univ u) (Set.mem_univ (v + x)) hα0 hβ0 hsum
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
      calc _ = (β + α) * h u + (α + β) * h (v + x) := by ring
        _ = _ := by rw [hsum', hsum]; ring
    linarith

lemma convex_shift_lin {h : ℝ → ℝ} (hh : ConvexOn ℝ Set.univ h) (c K : ℝ) :
    ConvexOn ℝ Set.univ (fun y => (h (c + y) - h c) - K * y) := by
  refine ⟨convex_univ, fun u _ v _ s1 t1 hs1 ht1 hst1 => ?_⟩
  have := hh.2 (Set.mem_univ (c + u)) (Set.mem_univ (c + v)) hs1 ht1 hst1
  simp only [smul_eq_mul] at this ⊢
  have e : s1 * (c + u) + t1 * (c + v) = c + (s1 * u + t1 * v) := by
    calc _ = (s1 + t1) * c + (s1 * u + t1 * v) := by ring
      _ = _ := by rw [hst1, one_mul]
  rw [e] at this
  have hc : (s1 + t1) * h c = h c := by rw [hst1, one_mul]
  nlinarith [this, hc]

noncomputable def Bs (b : ℕ → ℝ) (j : ℕ) : ℝ := ∑ l ∈ range j, b l
noncomputable def As (a : ℕ → ℝ) (j : ℕ) : ℝ := ∑ l ∈ range j, a l

/-- Main normalized z-step. -/
theorem ncz_main (n : ℕ) (a b : ℕ → ℝ) (b0 : ℝ) (hf : ℝ → ℝ) (h : WOrdN n a b)
    (hh : ConvexOn ℝ Set.univ hf) :
    ∃ z : ℕ → ℝ, (∀ l, l < n → a l = 0 → b l = 0 → z l = 0) ∧
      (∀ w : ℕ → ℝ, (∀ l, l < n → 0 ≤ w l ∧ w l ≤ 1) →
        hf (b0 + ∑ l ∈ range n, b l * w l) ≤ hf b0 + ∑ l ∈ range n, z l * w l) ∧
      WOrdN n (fun l => a l + z l) b ∧
      ∀ j, j ≤ n → ∃ j1, j1 ≤ n ∧ ∃ j2, j2 ≤ n ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
        ∑ l ∈ range j, (a l + z l) =
          (1 - μ) * (As a j1 + (hf (b0 + Bs b j1) - hf b0)) +
            μ * (As a j2 + (hf (b0 + Bs b j2) - hf b0)) ∧
        Bs b j = (1 - μ) * Bs b j1 + μ * Bs b j2 := by
  classical
  set Yz : ℕ → ℝ := fun j => As a j + (hf (b0 + Bs b j) - hf b0) with hYz
  have hδ0 : ∀ l, l < n → -b l ≤ (fun _ => (0 : ℝ)) l ∧ (fun _ => (0 : ℝ)) l ≤ 0 :=
    fun l hl => ⟨by have := h.1 l hl; simp; linarith, le_rfl⟩
  have hYB : ∀ j, Yp b (fun _ => 0) j = Bs b j := by intro j; simp [Yp, Bs]
  have hGA : ∀ j, Gp a (fun _ => 0) 0 j = As a j := by intro j; simp [Gp, As]
  obtain ⟨v0, hv0n, hlead, htop⟩ := lead_top (c := 0) h hδ0
  simp only [hYB, hGA, add_zero, mul_zero] at hlead htop
  set x : ℕ → ℝ := fun j => Bs b (min j n) with hxdef
  set y : ℕ → ℝ := fun j => Yz (min j n) with hydef
  have hxj : ∀ j, j ≤ n → x j = Bs b j := fun j hj => by simp [hxdef, min_eq_left hj]
  have hyj : ∀ j, j ≤ n → y j = Yz j := fun j hj => by simp [hydef, min_eq_left hj]
  have hBmono : ∀ i j, i ≤ j → j ≤ n → Bs b i ≤ Bs b j := by
    intro i j hij hjn; rw [← hYB, ← hYB]; exact Yp_mono hδ0 hij hjn
  have hxmono : Monotone x := by
    intro i j hij
    exact hBmono _ _ (min_le_min_right n hij) (min_le_right _ _)
  have hBv0 : Bs b v0 = 0 := by
    unfold Bs; exact Finset.sum_eq_zero (fun l hl => (hlead l (mem_range.1 hl)).1)
  obtain ⟨m, s, hH⟩ := hull_exists x y hxmono n (n - v0) v0 rfl hv0n (fun j hj hjn hxe => by
    rw [hxj j hjn, hxj v0 hv0n] at hxe
    rw [hyj j hjn, hyj v0 hv0n]
    simp only [hYz, hxe]
    have := htop j hj hjn hxe
    linarith)
  obtain ⟨hs0, hrng, hinc, hxinc, hanti, hbel, hlast⟩ := hH
  set e := s m with he
  have hen : e ≤ n := (hrng m le_rfl).2
  have hve : v0 ≤ e := (hrng m le_rfl).1
  have smono' : ∀ i j, i ≤ j → j ≤ m → s i ≤ s j := by
    intro i j hij hjm
    induction j with
    | zero => rw [Nat.le_zero.1 hij]
    | succ j ih =>
      rcases hij.lt_or_eq with h1 | h1
      · exact le_trans (ih (by omega) (by omega)) (hinc j (by omega)).le
      · rw [h1]
  -- trailing part
  have hBe : Bs b e = Bs b n := by
    rcases hen.lt_or_eq with h1 | h1
    · have := (hlast n h1 le_rfl).1
      rw [hxj n le_rfl, hxj e hen] at this
      exact this.symm
    · rw [h1]
  have htz : ∀ l, e ≤ l → l < n → b l = 0 := by
    intro l hl1 hl2
    have := zero_prog hδ0 hen le_rfl (by rw [hYB, hYB]; exact hBe) l hl1 hl2
    simpa using this
  have hta : ∀ l, e ≤ l → l < n → a l ≤ 0 := by
    intro l hl1 hl2
    by_contra hpos
    push Not at hpos
    have hnn : ∀ l', e ≤ l' → l' < l → 0 ≤ a l' := by
      intro l' h1 h2
      by_contra hneg
      push Not at hneg
      have hm := ml2 h 0 (show a l' < 0 * b l' by rw [zero_mul]; exact hneg)
      have := hm l h2.le hl2
      rw [zero_mul] at this
      linarith
    have hlt := (hlast (l + 1) (by omega) (by omega)).2
    rw [hyj (l + 1) (by omega), hyj e hen] at hlt
    have hB1 : Bs b (l + 1) = Bs b e := by
      have := (hlast (l + 1) (by omega) (by omega)).1
      rw [hxj (l + 1) (by omega), hxj e hen] at this; exact this
    simp only [hYz, hB1] at hlt
    have : As a (l + 1) - As a e ≥ a l := by
      unfold As
      rw [← Finset.sum_range_add_sum_Ico _ (show e ≤ l + 1 by omega), Finset.sum_Ico_succ_top hl1]
      have : 0 ≤ ∑ i ∈ Ico e l, a i := Finset.sum_nonneg (fun i hi => by
        rw [mem_Ico] at hi; exact hnn i hi.1 hi.2)
      linarith
    linarith
  -- slopes
  set K : ℕ → ℝ := fun i => sl x y (s i) (s (i + 1)) with hKdef
  have kanti : ∀ i j, i ≤ j → j < m → K j ≤ K i := by
    intro i j hij hjm
    induction j with
    | zero => rw [Nat.le_zero.1 hij]
    | succ j ih =>
      rcases hij.lt_or_eq with h1 | h1
      · exact le_trans (hanti j (by omega)) (ih (by omega) (by omega))
      · rw [h1]
  set bi : ℕ → ℕ := fun l => Nat.findGreatest (fun i => s i ≤ l) m with hbidef
  have bi_spec : ∀ l, v0 ≤ l → l < e → bi l < m ∧ s (bi l) ≤ l ∧ l < s (bi l + 1) := by
    intro l hl1 hl2
    have hP0 : s 0 ≤ l := by rw [hs0]; exact hl1
    have hspec : s (bi l) ≤ l := Nat.findGreatest_spec (P := fun i => s i ≤ l) (Nat.zero_le m) hP0
    have hle : bi l ≤ m := Nat.findGreatest_le m
    have hlt : bi l < m := by
      rcases hle.lt_or_eq with h1 | h1
      · exact h1
      · exfalso; rw [h1] at hspec; omega
    refine ⟨hlt, hspec, ?_⟩
    by_contra hc
    push Not at hc
    exact Nat.findGreatest_is_greatest (P := fun i => s i ≤ l) (Nat.lt_succ_self (bi l))
      (by omega) hc
  have bi_eq : ∀ i, i < m → ∀ l, s i ≤ l → l < s (i + 1) → bi l = i := by
    intro i hi l hl1 hl2
    have h1 : i ≤ bi l := Nat.le_findGreatest (P := fun i => s i ≤ l) hi.le hl1
    have hv : v0 ≤ l := by rw [← hs0]; exact le_trans (smono' 0 i (Nat.zero_le _) hi.le) hl1
    have he' : l < e := lt_of_lt_of_le hl2 (smono' (i + 1) m (by omega) le_rfl)
    obtain ⟨_, hsp, _⟩ := bi_spec l hv he'
    by_contra hne
    have h2 : i + 1 ≤ bi l := by omega
    have := smono' (i + 1) (bi l) h2 (Nat.findGreatest_le m)
    omega
  have bi_mono : ∀ l l', l ≤ l' → bi l ≤ bi l' := by
    intro l l' hll
    exact Nat.findGreatest_mono_left (fun i (hi : s i ≤ l) => le_trans hi hll) m
  -- block data
  have blk : ∀ i, i < m →
      Bs b (s i) < Bs b (s (i + 1)) ∧
      (∀ j, s i < j → j < s (i + 1) → Yz j - Yz (s i) ≤ K i * (Bs b j - Bs b (s i))) ∧
      Yz (s (i + 1)) - Yz (s i) = K i * (Bs b (s (i + 1)) - Bs b (s i)) := by
    intro i hi
    have hsi : s i ≤ n := (hrng i hi.le).2
    have hsi1 : s (i + 1) ≤ n := (hrng (i + 1) hi).2
    have hx := hxinc i hi
    rw [hxj _ hsi, hxj _ hsi1] at hx
    refine ⟨hx, fun j hj1 hj2 => ?_, ?_⟩
    · have hjn : j ≤ n := by omega
      have := hbel i hi j hj1 hj2
      rw [hxj j hjn, hxj _ hsi, hyj j hjn, hyj _ hsi] at this
      exact this
    · have := sl_spec x y (s i) (s (i + 1)) (hxinc i hi)
      rw [hxj _ hsi, hxj _ hsi1, hyj _ hsi, hyj _ hsi1] at this
      exact this
  -- the cost coefficients
  set z : ℕ → ℝ := fun l => if v0 ≤ l ∧ l < e then K (bi l) * b l - a l else 0 with hzdef
  have z_blk : ∀ i, i < m → ∀ l, s i ≤ l → l < s (i + 1) → z l = K i * b l - a l := by
    intro i hi l hl1 hl2
    have hv : v0 ≤ l := by rw [← hs0]; exact le_trans (smono' 0 i (Nat.zero_le _) hi.le) hl1
    have he' : l < e := lt_of_lt_of_le hl2 (smono' (i + 1) m (by omega) le_rfl)
    simp only [hzdef, hv, he', and_self, if_true, bi_eq i hi l hl1 hl2]
  have z_out : ∀ l, ¬ (v0 ≤ l ∧ l < e) → z l = 0 := by
    intro l hl; simp only [hzdef, hl, if_false]
  -- matching
  have hYzv0 : Yz v0 = As a v0 := by simp only [hYz, hBv0, add_zero, sub_self]
  have match_s : ∀ i, i ≤ m → ∑ l ∈ range (s i), (a l + z l) = Yz (s i) := by
    intro i hi
    induction i with
    | zero =>
      rw [hs0, hYzv0]
      unfold As
      exact Finset.sum_congr rfl (fun l hl => by
        rw [mem_range] at hl; rw [z_out l (by omega), add_zero])
    | succ i ih =>
      have hle := (hinc i (by omega)).le
      rw [← Finset.sum_range_add_sum_Ico _ hle, ih (by omega)]
      have hb : ∑ l ∈ Ico (s i) (s (i + 1)), (a l + z l) =
          ∑ l ∈ Ico (s i) (s (i + 1)), K i * b l :=
        Finset.sum_congr rfl (fun l hl => by
          rw [mem_Ico] at hl; rw [z_blk i (by omega) l hl.1 hl.2]; ring)
      rw [hb, ← Finset.mul_sum]
      have hBdiff : ∑ l ∈ Ico (s i) (s (i + 1)), b l = Bs b (s (i + 1)) - Bs b (s i) := by
        unfold Bs; rw [← Finset.sum_range_add_sum_Ico _ hle]; ring
      rw [hBdiff]
      have := (blk i (by omega)).2.2
      linarith
  -- the generator shapes
  have gen_lead : ∀ l, l < v0 → b l = 0 ∧ 0 ≤ a l + z l := by
    intro l hl
    rw [z_out l (by omega), add_zero]; exact hlead l hl
  have gen_trail : ∀ l, e ≤ l → l < n → b l = 0 ∧ a l + z l ≤ 0 := by
    intro l hl1 hl2
    rw [z_out l (by omega), add_zero]; exact ⟨htz l hl1 hl2, hta l hl1 hl2⟩
  have gen_blk : ∀ l, v0 ≤ l → l < e → a l + z l = K (bi l) * b l := by
    intro l hl1 hl2
    obtain ⟨h1, h2, h3⟩ := bi_spec l hl1 hl2
    rw [z_blk (bi l) h1 l h2 h3]; ring
  refine ⟨z, fun l hl ha hb => ?_, ?_, ?_, ?_⟩
  · by_cases hin : v0 ≤ l ∧ l < e
    · simp only [hzdef, hin, and_self, if_true, ha, hb, mul_zero, sub_zero]
    · exact z_out l hin
  · -- domination z ≥ h
    intro w hw
    set Bw : ℕ → ℝ := fun j => ∑ l ∈ range j, b l * w l with hBw
    set Zw : ℕ → ℝ := fun j => ∑ l ∈ range j, z l * w l with hZw
    have hBwle : ∀ j, j ≤ n → Bw j ≤ Bs b j := by
      intro j hj
      exact Finset.sum_le_sum (fun l hl => by
        rw [mem_range] at hl
        have := h.1 l (by omega); have := hw l (by omega); nlinarith)
    have claim : ∀ i, i ≤ m → hf (b0 + Bw (s i)) - hf b0 ≤ Zw (s i) := by
      intro i hi
      induction i with
      | zero =>
        rw [hs0]
        have h1 : Bw v0 = 0 := Finset.sum_eq_zero (fun l hl => by
          rw [(hlead l (mem_range.1 hl)).1, zero_mul])
        have h2 : Zw v0 = 0 := Finset.sum_eq_zero (fun l hl => by
          rw [z_out l (by rw [mem_range] at hl; omega), zero_mul])
        rw [h1, h2, add_zero, sub_self]
      | succ i ih =>
        have hi' : i < m := by omega
        have ih' := ih hi'.le
        set p := s i with hp
        set r := s (i + 1) with hr
        have hpr : p ≤ r := (hinc i hi').le
        have hrn : r ≤ n := (hrng (i + 1) hi').2
        have hpn : p ≤ n := (hrng i hi'.le).2
        set β := ∑ l ∈ Ico p r, b l * w l with hβ
        set α := ∑ l ∈ Ico p r, a l * w l with hα
        have hβ0 : 0 ≤ β := Finset.sum_nonneg (fun l hl => by
          rw [mem_Ico] at hl
          have := h.1 l (by omega); have := hw l (by omega); nlinarith)
        have hBwr : Bw r = Bw p + β := by
          simp only [hBw, hβ]; rw [← Finset.sum_range_add_sum_Ico _ hpr]
        have hZwr : Zw r = Zw p + (K i * β - α) := by
          simp only [hZw, hβ, hα]
          rw [← Finset.sum_range_add_sum_Ico _ hpr, Finset.mul_sum, ← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl (fun l hl => by
            rw [mem_Ico] at hl; rw [z_blk i hi' l hl.1 hl.2]; ring)
        -- incr_mono
        have hinc1 := incr_mono hh (x := β) hβ0 (show b0 + Bw p ≤ b0 + Bs b p by
          linarith [hBwle p hpn])
        -- block bound via wl41n on the shifted block
        have hWb : WOrdN (r - p) (fun l => a (p + l)) (fun l => b (p + l)) :=
          ⟨fun l hl => h.1 _ (by omega), fun i' j' hij hj => h.2.1 _ _ (by omega) (by omega),
            fun i' j' hij hj => h.2.2 _ _ (by omega) (by omega)⟩
        obtain ⟨j', hj', hbd⟩ := wl41n (r - p) (fun l => a (p + l)) (fun l => b (p + l)) hWb
          (fun t => (hf ((b0 + Bs b p) + t) - hf (b0 + Bs b p)) - K i * t)
          (convex_shift_lin hh _ _) (fun l => w (p + l))
          (fun l hl => hw (p + l) (by omega))
        have eA : ∑ l ∈ range (r - p), a (p + l) * w (p + l) = α := by
          rw [hα, Finset.sum_Ico_eq_sum_range]
        have eB : ∑ l ∈ range (r - p), b (p + l) * w (p + l) = β := by
          rw [hβ, Finset.sum_Ico_eq_sum_range]
        have eA' : ∑ l ∈ range j', a (p + l) = As a (p + j') - As a p := by
          unfold As
          rw [← Finset.sum_range_add_sum_Ico _ (show p ≤ p + j' by omega),
            Finset.sum_Ico_eq_sum_range]
          simp
        have eB' : ∑ l ∈ range j', b (p + l) = Bs b (p + j') - Bs b p := by
          unfold Bs
          rw [← Finset.sum_range_add_sum_Ico _ (show p ≤ p + j' by omega),
            Finset.sum_Ico_eq_sum_range]
          simp
        try beta_reduce at hbd
        rw [eA, eB, eA', eB'] at hbd
        -- the block prefix value is ≤ 0
        have hpv : (As a (p + j') - As a p) +
            ((hf ((b0 + Bs b p) + (Bs b (p + j') - Bs b p)) - hf (b0 + Bs b p)) -
              K i * (Bs b (p + j') - Bs b p)) ≤ 0 := by
          have eq1 : (b0 + Bs b p) + (Bs b (p + j') - Bs b p) = b0 + Bs b (p + j') := by ring
          rw [eq1]
          have key : Yz (p + j') - Yz p ≤ K i * (Bs b (p + j') - Bs b p) := by
            rcases Nat.eq_zero_or_pos j' with h0 | hpos
            · rw [h0, add_zero]; simp
            · rcases (show p + j' ≤ r by omega).lt_or_eq with hlt | heq
              · exact (blk i hi').2.1 (p + j') (by omega) hlt
              · rw [heq]; exact (blk i hi').2.2.le
          simp only [hYz] at key
          linarith
        have hfin : hf (b0 + Bw r) - hf b0 ≤ Zw r := by
          rw [hBwr, hZwr]
          have e2 : b0 + (Bw p + β) = (b0 + Bw p) + β := by ring
          rw [e2]
          linarith
        exact hfin
    have hfinal := claim m le_rfl
    have hBn : Bw n = Bw e := by
      simp only [hBw]
      rw [← Finset.sum_range_add_sum_Ico _ hen]
      have : ∑ l ∈ Ico e n, b l * w l = 0 := Finset.sum_eq_zero (fun l hl => by
        rw [mem_Ico] at hl; rw [htz l hl.1 hl.2, zero_mul])
      rw [this, add_zero]
    have hZn : Zw n = Zw e := by
      simp only [hZw]
      rw [← Finset.sum_range_add_sum_Ico _ hen]
      have : ∑ l ∈ Ico e n, z l * w l = 0 := Finset.sum_eq_zero (fun l hl => by
        rw [mem_Ico] at hl; rw [z_out l (by omega), zero_mul])
      rw [this, add_zero]
    have : hf (b0 + Bw n) ≤ hf b0 + Zw n := by rw [hBn, hZn]; linarith
    exact this
  · -- weak order of the new generators
    refine ⟨h.1, ?_, ?_⟩
    · intro i j hij hjn
      show (a j + z j) * b i ≤ (a i + z i) * b j
      by_cases hi : i < v0
      · obtain ⟨h1, h2⟩ := gen_lead i hi
        rw [h1]
        have := h.1 j hjn
        nlinarith
      · by_cases hj : e ≤ j
        · obtain ⟨h1, h2⟩ := gen_trail j hj hjn
          rw [h1]
          have := h.1 i (by omega)
          nlinarith
        · rw [gen_blk i (by omega) (by omega), gen_blk j (by omega) (by omega)]
          have hK : K (bi j) ≤ K (bi i) :=
            kanti (bi i) (bi j) (bi_mono i j hij.le) (bi_spec j (by omega) (by omega)).1
          have := mul_nonneg (h.1 i (by omega)) (h.1 j hjn)
          nlinarith
    · intro i j hij hjn hbi0 hbj0
      show a j + z j ≤ 0 ∨ 0 ≤ a i + z i
      by_cases hi : i < v0
      · right; exact (gen_lead i hi).2
      · by_cases hj : e ≤ j
        · left; exact (gen_trail j hj hjn).2
        · right
          rw [gen_blk i (by omega) (by omega), hbi0, mul_zero]
  · -- convex combinations
    intro j hjn
    have matched : ∀ j', j' ≤ n → ∑ l ∈ range j', (a l + z l) = Yz j' →
        ∃ j1, j1 ≤ n ∧ ∃ j2, j2 ≤ n ∧ ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
          ∑ l ∈ range j', (a l + z l) =
            (1 - μ) * (As a j1 + (hf (b0 + Bs b j1) - hf b0)) +
              μ * (As a j2 + (hf (b0 + Bs b j2) - hf b0)) ∧
          Bs b j' = (1 - μ) * Bs b j1 + μ * Bs b j2 := by
      intro j' hj' hm
      refine ⟨j', hj', j', hj', 0, le_rfl, zero_le_one, ?_, by ring⟩
      rw [hm]; simp only [hYz]; ring
    by_cases h1 : j ≤ v0
    · apply matched j hjn
      have hB : Bs b j = 0 := by
        unfold Bs; exact Finset.sum_eq_zero (fun l hl => (hlead l (by rw [mem_range] at hl; omega)).1)
      simp only [hYz, hB, add_zero, sub_self]
      unfold As
      exact Finset.sum_congr rfl (fun l hl => by
        rw [mem_range] at hl; rw [z_out l (by omega), add_zero])
    · by_cases h2 : e ≤ j
      · apply matched j hjn
        rw [← Finset.sum_range_add_sum_Ico _ h2, match_s m le_rfl]
        have hz0 : ∑ l ∈ Ico e j, (a l + z l) = ∑ l ∈ Ico e j, a l :=
          Finset.sum_congr rfl (fun l hl => by
            rw [mem_Ico] at hl; rw [z_out l (by omega), add_zero])
        have hBj : Bs b j = Bs b e := by
          unfold Bs
          rw [← Finset.sum_range_add_sum_Ico _ h2]
          have : ∑ l ∈ Ico e j, b l = 0 := Finset.sum_eq_zero (fun l hl => by
            rw [mem_Ico] at hl; exact htz l hl.1 (by omega))
          rw [this, add_zero]
        rw [hz0]
        simp only [hYz, hBj]
        unfold As
        rw [← Finset.sum_range_add_sum_Ico a h2]
        ring
      · obtain ⟨hi, hsj, hjs⟩ := bi_spec j (by omega) (by omega)
        set i := bi j
        set p := s i
        set r := s (i + 1)
        have hrn : r ≤ n := (hrng (i + 1) hi).2
        have hpn : p ≤ n := (hrng i hi.le).2
        obtain ⟨hY, _, hend⟩ := blk i hi
        have hmp := match_s i hi.le
        have hpartA : ∑ l ∈ range j, (a l + z l) = Yz p + K i * (Bs b j - Bs b p) := by
          rw [← Finset.sum_range_add_sum_Ico _ hsj, hmp]
          have : ∑ l ∈ Ico p j, (a l + z l) = ∑ l ∈ Ico p j, K i * b l :=
            Finset.sum_congr rfl (fun l hl => by
              rw [mem_Ico] at hl; rw [z_blk i hi l hl.1 (by omega)]; ring)
          rw [this, ← Finset.mul_sum]
          congr 2
          unfold Bs; rw [← Finset.sum_range_add_sum_Ico _ hsj]; ring
        set D := Bs b r - Bs b p with hD
        have hDpos : 0 < D := by rw [hD]; linarith
        have hS0 : 0 ≤ Bs b j - Bs b p := by linarith [hBmono p j hsj (by omega)]
        have hSle : Bs b j - Bs b p ≤ D := by rw [hD]; linarith [hBmono j r hjs.le hrn]
        refine ⟨p, hpn, r, hrn, (Bs b j - Bs b p) / D, div_nonneg hS0 hDpos.le,
          (div_le_one hDpos).2 hSle, ?_, ?_⟩
        · rw [hpartA]
          have hYr : Yz r = Yz p + K i * D := by rw [hD]; linarith
          have e1 : As a p + (hf (b0 + Bs b p) - hf b0) = Yz p := rfl
          have e2 : As a r + (hf (b0 + Bs b r) - hf b0) = Yz r := rfl
          rw [e1, e2, hYr]
          field_simp
          ring
        · have : Bs b r = Bs b p + D := by rw [hD]; ring
          rw [this]
          field_simp
          ring

end P172Z

namespace P172N

open Finset P172H P172Q P172Z

/-- Normalized q-step: with any policy law `u` that is `[L, U]`-valued, nonincreasing and
1-Lipschitz (the clamp law, or the constant `L`), an affine policy exists on the cube that is
feasible and keeps `θ₁ + c q + g(θ₂ + q)` below any `V` dominating the chain-vertex values. -/
theorem nq_step (n : ℕ) (a b : ℕ → ℝ) (h : WOrdN n a b) (a0 b0 c L U : ℝ) (u : ℝ → ℝ)
    (hu : ∀ x, L ≤ u x ∧ u x ≤ U)
    (hlip : ∀ x t, 0 ≤ t → -t ≤ u (x + t) - u x ∧ u (x + t) - u x ≤ 0)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) (V : ℝ)
    (hV : ∀ j, j ≤ n → a0 + As a j + c * u (b0 + Bs b j) +
      g (b0 + Bs b j + u (b0 + Bs b j)) ≤ V) :
    ∃ (q0 : ℝ) (q : ℕ → ℝ), (∀ l, l < n → b l = 0 → q l = 0) ∧
      ∀ w : ℕ → ℝ, (∀ l, l < n → 0 ≤ w l ∧ w l ≤ 1) →
      (L ≤ q0 + ∑ l ∈ range n, q l * w l ∧ q0 + ∑ l ∈ range n, q l * w l ≤ U) ∧
      (a0 + ∑ l ∈ range n, a l * w l) + c * (q0 + ∑ l ∈ range n, q l * w l) +
        g (b0 + ∑ l ∈ range n, b l * w l + (q0 + ∑ l ∈ range n, q l * w l)) ≤ V := by
  set X : ℕ → ℝ := fun j => b0 + Bs b j with hX
  have hXs : ∀ l, X (l + 1) = X l + b l := by
    intro l; simp only [hX, Bs, Finset.sum_range_succ]; ring
  set δ : ℕ → ℝ := fun l => u (X (l + 1)) - u (X l) with hδdef
  have hδ : ∀ l, l < n → -b l ≤ δ l ∧ δ l ≤ 0 := by
    intro l hl
    simp only [hδdef, hXs]
    exact hlip (X l) (b l) (h.1 l hl)
  obtain ⟨q, hqb, hqsum, hqord, hcomb⟩ := ncq_main n a b δ c h hδ
  have htel : ∀ j, ∑ l ∈ range j, δ l = u (X j) - u b0 := by
    intro j
    simp only [hδdef]
    rw [Finset.sum_range_sub (fun l => u (X l))]
    simp [hX, Bs]
  refine ⟨u b0, q, fun l hl hb => ?_, fun w hw => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have := hqb l hl; rw [hb] at this; linarith [this.1, this.2]
  · have h1 : ∑ l ∈ range n, q l ≤ ∑ l ∈ range n, q l * w l :=
      Finset.sum_le_sum (fun l hl => by
        rw [mem_range] at hl
        have := hqb l hl; have := hw l hl; nlinarith)
    rw [hqsum, htel] at h1
    have := (hu (X n)).1
    linarith
  · have h1 : ∑ l ∈ range n, q l * w l ≤ 0 :=
      Finset.sum_nonpos (fun l hl => by
        rw [mem_range] at hl
        have := hqb l hl; have := hw l hl; nlinarith)
    have := (hu b0).2
    linarith
  · -- value bound
    have hgs : ConvexOn ℝ Set.univ (fun t => g (b0 + u b0 + t)) := by
      refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
      have := hg.2 (Set.mem_univ (b0 + u b0 + x)) (Set.mem_univ (b0 + u b0 + y)) hs ht hst
      simp only [smul_eq_mul] at this ⊢
      have e : s * (b0 + u b0 + x) + t * (b0 + u b0 + y) = b0 + u b0 + (s * x + t * y) := by
        calc _ = (s + t) * (b0 + u b0) + (s * x + t * y) := by ring
          _ = _ := by rw [hst, one_mul]
      rw [e] at this; exact this
    obtain ⟨j, hj, hle⟩ := wl41n n (fun l => a l + c * q l) (fun l => b l + q l) hqord
      (fun t => g (b0 + u b0 + t)) hgs w hw
    obtain ⟨j1, hj1, j2, hj2, μ, hμ0, hμ1, hA, hB⟩ := hcomb j hj
    have hGp : ∀ jk, Gp a δ c jk = As a jk + c * (u (X jk) - u b0) := by
      intro jk
      unfold Gp As
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, htel]
    have hYp : ∀ jk, Yp b δ jk = Bs b jk + (u (X jk) - u b0) := by
      intro jk
      unfold Yp Bs
      rw [Finset.sum_add_distrib, htel]
    have hP : ∀ jk, jk ≤ n → a0 + c * u b0 + Gp a δ c jk + g (b0 + u b0 + Yp b δ jk) ≤ V := by
      intro jk hjk
      rw [hGp, hYp]
      have := hV jk hjk
      have e : b0 + u b0 + (Bs b jk + (u (X jk) - u b0)) = b0 + Bs b jk + u (b0 + Bs b jk) := by
        simp only [hX]; ring
      rw [e]
      have e2 : u (X jk) = u (b0 + Bs b jk) := rfl
      rw [e2]
      linarith
    have hP1 := hP j1 hj1
    have hP2 := hP j2 hj2
    have hconv := hgs.2 (Set.mem_univ (Yp b δ j1)) (Set.mem_univ (Yp b δ j2))
      (sub_nonneg.2 hμ1) hμ0 (by ring)
    simp only [smul_eq_mul] at hconv
    try beta_reduce at hle
    rw [hA, hB] at hle
    have eA : ∑ l ∈ range n, (a l + c * q l) * w l =
        ∑ l ∈ range n, a l * w l + c * ∑ l ∈ range n, q l * w l := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have eB : ∑ l ∈ range n, (b l + q l) * w l =
        ∑ l ∈ range n, b l * w l + ∑ l ∈ range n, q l * w l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [eA, eB] at hle
    have e3 : b0 + ∑ l ∈ range n, b l * w l + (u b0 + ∑ l ∈ range n, q l * w l) =
        b0 + u b0 + (∑ l ∈ range n, b l * w l + ∑ l ∈ range n, q l * w l) := by ring
    rw [e3]
    have hm1 : (1 - μ) * (a0 + c * u b0 + Gp a δ c j1 + g (b0 + u b0 + Yp b δ j1)) ≤ (1 - μ) * V :=
      mul_le_mul_of_nonneg_left hP1 (sub_nonneg.2 hμ1)
    have hm2 : μ * (a0 + c * u b0 + Gp a δ c j2 + g (b0 + u b0 + Yp b δ j2)) ≤ μ * V :=
      mul_le_mul_of_nonneg_left hP2 hμ0
    nlinarith [hle, hconv, hm1, hm2]

end P172N

namespace P172N

open Finset P172H P172Q P172Z

/-- Normalized z-step: an affine cost dominating `h` on the cube that keeps
`θ₁ + z + J'(θ₂)` below any `V` dominating the chain-vertex values of `θ₁ + h(θ₂) + J'(θ₂)`. -/
theorem nz_step (n : ℕ) (a b : ℕ → ℝ) (h : WOrdN n a b) (a0 b0 : ℝ) (hf Jp : ℝ → ℝ)
    (hh : ConvexOn ℝ Set.univ hf) (hJ : ConvexOn ℝ Set.univ Jp) (V : ℝ)
    (hV : ∀ j, j ≤ n → a0 + As a j + hf (b0 + Bs b j) + Jp (b0 + Bs b j) ≤ V) :
    ∃ (z0 : ℝ) (z : ℕ → ℝ), (∀ l, l < n → a l = 0 → b l = 0 → z l = 0) ∧
      ∀ w : ℕ → ℝ, (∀ l, l < n → 0 ≤ w l ∧ w l ≤ 1) →
      hf (b0 + ∑ l ∈ range n, b l * w l) ≤ z0 + ∑ l ∈ range n, z l * w l ∧
      (a0 + ∑ l ∈ range n, a l * w l) + (z0 + ∑ l ∈ range n, z l * w l) +
        Jp (b0 + ∑ l ∈ range n, b l * w l) ≤ V := by
  obtain ⟨z, hz0, hdom, hord, hcomb⟩ := ncz_main n a b b0 hf h hh
  refine ⟨hf b0, z, hz0, fun w hw => ⟨hdom w hw, ?_⟩⟩
  have hJs : ConvexOn ℝ Set.univ (fun t => Jp (b0 + t)) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    have := hJ.2 (Set.mem_univ (b0 + x)) (Set.mem_univ (b0 + y)) hs ht hst
    simp only [smul_eq_mul] at this ⊢
    have e : s * (b0 + x) + t * (b0 + y) = b0 + (s * x + t * y) := by
      calc _ = (s + t) * b0 + (s * x + t * y) := by ring
        _ = _ := by rw [hst, one_mul]
    rw [e] at this; exact this
  obtain ⟨j, hj, hle⟩ := wl41n n (fun l => a l + z l) b hord (fun t => Jp (b0 + t)) hJs w hw
  obtain ⟨j1, hj1, j2, hj2, μ, hμ0, hμ1, hA, hB⟩ := hcomb j hj
  try beta_reduce at hle
  have hBs : ∑ l ∈ range j, b l = Bs b j := rfl
  rw [hA, hBs, hB] at hle
  have hconv := hJs.2 (Set.mem_univ (Bs b j1)) (Set.mem_univ (Bs b j2))
    (sub_nonneg.2 hμ1) hμ0 (by ring)
  simp only [smul_eq_mul] at hconv
  have eA : ∑ l ∈ range n, (a l + z l) * w l =
      ∑ l ∈ range n, a l * w l + ∑ l ∈ range n, z l * w l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [eA] at hle
  have hP1 := hV j1 hj1
  have hP2 := hV j2 hj2
  have hm1 : (1 - μ) * (a0 + As a j1 + hf (b0 + Bs b j1) + Jp (b0 + Bs b j1)) ≤ (1 - μ) * V :=
    mul_le_mul_of_nonneg_left hP1 (sub_nonneg.2 hμ1)
  have hm2 : μ * (a0 + As a j2 + hf (b0 + Bs b j2) + Jp (b0 + Bs b j2)) ≤ μ * V :=
    mul_le_mul_of_nonneg_left hP2 hμ0
  nlinarith [hle, hconv, hm1, hm2]

end P172N

namespace P172S

open Finset P172Q

lemma kappa_ord (ai bi aj bj : ℝ) (hi : 0 ≤ bi) (hi' : bi = 0 → 0 ≤ ai) (hj : 0 ≤ bj)
    (hj' : bj = 0 → 0 ≤ aj) (h : -ai / (|ai| + bi) ≤ -aj / (|aj| + bj)) : aj * bi ≤ ai * bj := by
  rcases (add_nonneg (abs_nonneg ai) hi).eq_or_lt with hDi | hDi
  · have h1 : |ai| = 0 := by linarith [abs_nonneg ai]
    have h2 : bi = 0 := by linarith [abs_nonneg ai]
    rw [abs_eq_zero] at h1
    rw [h1, h2]; simp
  rcases (add_nonneg (abs_nonneg aj) hj).eq_or_lt with hDj | hDj
  · have h1 : |aj| = 0 := by linarith [abs_nonneg aj]
    have h2 : bj = 0 := by linarith [abs_nonneg aj]
    rw [abs_eq_zero] at h1
    rw [h1, h2]; simp
  rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ hDj hDi] at h
  rcases le_total 0 ai with hai | hai <;> rcases le_total 0 aj with haj | haj
  · rw [abs_of_nonneg hai, abs_of_nonneg haj] at h; nlinarith
  · nlinarith
  · -- ai ≤ 0 ≤ aj
    rw [abs_of_nonpos hai, abs_of_nonneg haj] at h
    nlinarith [mul_nonneg haj hDi.le, mul_nonneg (neg_nonneg.2 hai) hDj.le]
  · rw [abs_of_nonpos hai, abs_of_nonpos haj] at h; nlinarith

/-- ℕ-extension of a `Fin T` tuple by zero. -/
noncomputable def ext {T : ℕ} (f : Fin T → ℝ) (l : ℕ) : ℝ := if h : l < T then f ⟨l, h⟩ else 0

lemma ext_fin {T : ℕ} (f : Fin T → ℝ) (i : Fin T) : ext f i = f i := by
  simp [ext, i.2]

lemma sum_ext {T : ℕ} (f g : Fin T → ℝ) :
    ∑ l ∈ range T, ext f l * ext g l = ∑ i : Fin T, f i * g i := by
  rw [← Fin.sum_univ_eq_sum_range (fun l => ext f l * ext g l) T]
  simp [ext_fin]

/-- The normalization S1: flip each coordinate so its generator points right (or up with
nonneg cost), then sort by the angle key. -/
theorem s1 (T : ℕ) (lo hi α β : Fin T → ℝ) (hlh : ∀ t, lo t ≤ hi t) :
    ∃ (a b : ℕ → ℝ) (C1 C2 : ℝ) (s : (Fin T → ℝ) → ℕ → ℝ),
      WOrdN T a b ∧
      (∀ w : Fin T → ℝ, (∀ t, lo t ≤ w t ∧ w t ≤ hi t) → ∀ l, l < T → 0 ≤ s w l ∧ s w l ≤ 1) ∧
      (∀ w : Fin T → ℝ, (∀ t, lo t ≤ w t ∧ w t ≤ hi t) →
        ∑ t, α t * w t = C1 + ∑ l ∈ range T, a l * s w l ∧
        ∑ t, β t * w t = C2 + ∑ l ∈ range T, b l * s w l) ∧
      (∀ v : ℕ → ℝ, (∀ l, l < T → 0 ≤ v l ∧ v l ≤ 1) → ∃ w : Fin T → ℝ,
        (∀ t, lo t ≤ w t ∧ w t ≤ hi t) ∧
        ∑ t, α t * w t = C1 + ∑ l ∈ range T, a l * v l ∧
        ∑ t, β t * w t = C2 + ∑ l ∈ range T, b l * v l) ∧
      (∀ (r0 : ℝ) (r : ℕ → ℝ), (∀ l, l < T → a l = 0 → b l = 0 → r l = 0) →
        ∃ (c0 : ℝ) (cf : Fin T → ℝ), (∀ t, α t = 0 → β t = 0 → cf t = 0) ∧
          ∀ w : Fin T → ℝ, c0 + ∑ t, cf t * w t = r0 + ∑ l ∈ range T, r l * s w l) := by
  classical
  set W : Fin T → ℝ := fun t => hi t - lo t with hW
  have hW0 : ∀ t, 0 ≤ W t := fun t => by simp only [hW]; linarith [hlh t]
  set fl : Fin T → Prop := fun t => β t * W t < 0 ∨ (β t * W t = 0 ∧ α t * W t < 0) with hfl
  set na : Fin T → ℝ := fun t => if fl t then -(α t * W t) else α t * W t with hna
  set nb : Fin T → ℝ := fun t => if fl t then -(β t * W t) else β t * W t with hnb
  have hnb0 : ∀ t, 0 ≤ nb t := by
    intro t; simp only [hnb]
    split_ifs with hf
    · rcases hf with h1 | ⟨h1, _⟩ <;> linarith
    · simp only [hfl, not_or, not_and, not_lt] at hf
      exact hf.1
  have hnb' : ∀ t, nb t = 0 → 0 ≤ na t := by
    intro t ht; simp only [hnb, hna] at ht ⊢
    split_ifs at ht ⊢ with hf
    · rcases hf with h1 | ⟨_, h2⟩
      · linarith
      · linarith
    · simp only [hfl, not_or, not_and, not_lt] at hf
      exact hf.2 ht
  set κ : Fin T → ℝ := fun t => -na t / (|na t| + nb t) with hκ
  set σ : Equiv.Perm (Fin T) := Tuple.sort κ with hσ
  have hmono : Monotone (κ ∘ σ) := Tuple.monotone_sort κ
  set e : Fin T → (Fin T → ℝ) → ℝ := fun t w =>
    if fl t then (hi t - w t) / W t else (w t - lo t) / W t with he
  refine ⟨ext (fun i => na (σ i)), ext (fun i => nb (σ i)),
    ∑ t, (α t * lo t + if fl t then α t * W t else 0),
    ∑ t, (β t * lo t + if fl t then β t * W t else 0),
    fun w => ext (fun i => e (σ i) w), ?_, ?_, ?_, ?_, ?_⟩
  · -- weak order
    refine ⟨fun l hl => ?_, fun i j hij hj => ?_, fun i j hij hj hbi hbj => ?_⟩
    · simp only [ext, hl, dif_pos]; exact hnb0 _
    · simp only [ext, hj, show i < T by omega, dif_pos]
      have hk := hmono (show (⟨i, by omega⟩ : Fin T) ≤ ⟨j, hj⟩ from Fin.mk_le_mk.2 hij.le)
      simp only [Function.comp] at hk
      exact kappa_ord _ _ _ _ (hnb0 _) (hnb' _) (hnb0 _) (hnb' _) hk
    · right
      simp only [ext, show i < T by omega, dif_pos] at hbi ⊢
      exact hnb' _ hbi
  · -- encoder in the cube
    intro w hw l hl
    simp only [ext, hl, dif_pos, he]
    set t := σ ⟨l, hl⟩
    rcases (hW0 t).eq_or_lt with h0 | hpos
    · split_ifs <;> rw [← h0] <;> simp
    · split_ifs
      · exact ⟨div_nonneg (by linarith [(hw t).2]) hpos.le,
          (div_le_one hpos).2 (by simp only [hW]; linarith [(hw t).1])⟩
      · exact ⟨div_nonneg (by linarith [(hw t).1]) hpos.le,
          (div_le_one hpos).2 (by simp only [hW]; linarith [(hw t).2])⟩
  · -- the affine identities on the box
    intro w hw
    have key : ∀ (γ : Fin T → ℝ) (nγ : Fin T → ℝ),
        (∀ t, nγ t = if fl t then -(γ t * W t) else γ t * W t) →
        ∑ t, γ t * w t = ∑ t, (γ t * lo t + if fl t then γ t * W t else 0) +
          ∑ l ∈ range T, ext (fun i => nγ (σ i)) l * ext (fun i => e (σ i) w) l := by
      intro γ nγ hnγ
      rw [sum_ext, Equiv.sum_comp σ (fun t => nγ t * e t w), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [hnγ t]
      simp only [he]
      rcases (hW0 t).eq_or_lt with h0 | hpos
      · have hwt : w t = lo t := by
          have := hw t; simp only [hW] at h0; linarith [this.1, this.2]
        rw [hwt]; split_ifs <;> rw [← h0] <;> simp
      · have hne : W t ≠ 0 := hpos.ne'
        split_ifs
        · field_simp; simp only [hW]; ring
        · field_simp; ring
    exact ⟨key α na (fun t => rfl), key β nb (fun t => rfl)⟩
  · -- decoder
    intro v hv
    have hv1 : ∀ t : Fin T, 0 ≤ v (σ.symm t) ∧ v (σ.symm t) ≤ 1 := fun t => hv _ (σ.symm t).2
    refine ⟨fun t => if fl t then hi t - W t * v (σ.symm t) else lo t + W t * v (σ.symm t),
      fun t => ?_, ?_⟩
    · have h1 := hv1 t
      have h2 := hW0 t
      have h3 : W t = hi t - lo t := rfl
      beta_reduce
      split_ifs
      · constructor <;> nlinarith
      · constructor <;> nlinarith
    · have key : ∀ (γ : Fin T → ℝ) (nγ : Fin T → ℝ),
          (∀ t, nγ t = if fl t then -(γ t * W t) else γ t * W t) →
          ∑ t, γ t * (if fl t then hi t - W t * v (σ.symm t) else lo t + W t * v (σ.symm t)) =
            ∑ t, (γ t * lo t + if fl t then γ t * W t else 0) +
              ∑ l ∈ range T, ext (fun i => nγ (σ i)) l * v l := by
        intro γ nγ hnγ
        have hv' : ∑ l ∈ range T, ext (fun i => nγ (σ i)) l * v l =
            ∑ l ∈ range T, ext (fun i => nγ (σ i)) l * ext (fun i : Fin T => v i) l :=
          Finset.sum_congr rfl (fun l hl => by
            rw [mem_range] at hl; simp [ext, hl])
        rw [hv', sum_ext, ← Equiv.sum_comp σ.symm (fun i => nγ (σ i) * v i),
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        simp only [Equiv.apply_symm_apply]
        rw [hnγ t]
        have h3 : W t = hi t - lo t := rfl
        split_ifs
        · rw [h3]; ring
        · ring
      exact ⟨key α na (fun t => rfl), key β nb (fun t => rfl)⟩
  · -- pull-back of affine functions
    intro r0 r hr
    refine ⟨r0 + ∑ t, (if fl t then r (σ.symm t) * hi t / W t else -(r (σ.symm t) * lo t / W t)),
      fun t => if fl t then -(r (σ.symm t) / W t) else r (σ.symm t) / W t, ?_, ?_⟩
    · intro t hα hβ
      have hz : r (σ.symm t) = 0 := by
        apply hr _ (σ.symm t).2
        · rw [ext_fin]; simp only [Equiv.apply_symm_apply, hna, hα, zero_mul, neg_zero, ite_self]
        · rw [ext_fin]; simp only [Equiv.apply_symm_apply, hnb, hβ, zero_mul, neg_zero, ite_self]
      simp [hz]
    · intro w
      have hr' : ∑ l ∈ range T, r l * ext (fun i => e (σ i) w) l =
          ∑ l ∈ range T, ext (fun i : Fin T => r i) l * ext (fun i => e (σ i) w) l :=
        Finset.sum_congr rfl (fun l hl => by
          rw [mem_range] at hl; simp [ext, hl])
      show r0 + ∑ t, (if fl t then r (σ.symm t) * hi t / W t else -(r (σ.symm t) * lo t / W t)) +
          ∑ t, (if fl t then -(r (σ.symm t) / W t) else r (σ.symm t) / W t) * w t =
        r0 + ∑ l ∈ range T, r l * ext (fun i => e (σ i) w) l
      rw [hr', sum_ext, ← Equiv.sum_comp σ.symm (fun i => r i * e (σ i) w), add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      simp only [Equiv.apply_symm_apply, he]
      split_ifs <;> ring

end P172S

namespace P172L71

open AffinePolicyOpt.OneDim Set

lemma cont_of_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) : Continuous f :=
  continuousOn_univ.mp (hf.continuousOn isOpen_univ)

lemma bddAbove_shift {f : ℝ → ℝ} (hf : Continuous f) (y a b : ℝ) :
    BddAbove ((fun w => f (y + w)) '' Icc a b) :=
  (isCompact_Icc.image (hf.comp (continuous_const.add continuous_id))).bddAbove

lemma sup_attain {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    ∃ w ∈ Icc a b, sSup ((fun w => f (y + w)) '' Icc a b) = f (y + w) := by
  obtain ⟨w, hw, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab)
    ((hf.comp (continuous_const.add continuous_id)).continuousOn : ContinuousOn (fun w => f (y + w)) (Icc a b))
  refine ⟨w, hw, ?_⟩
  apply IsGreatest.csSup_eq
  exact ⟨⟨w, hw, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact hmax hv⟩

lemma sup_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {a b : ℝ} (hab : a ≤ b) :
    ConvexOn ℝ univ (fun y => sSup ((fun w => f (y + w)) '' Icc a b)) := by
  have hfc := cont_of_convex hf
  refine ⟨convex_univ, fun y1 _ y2 _ s t hs ht hst => ?_⟩
  have hne : ((fun w => f (s • y1 + t • y2 + w)) '' Icc a b).Nonempty :=
    ⟨_, a, left_mem_Icc.2 hab, rfl⟩
  apply csSup_le hne
  rintro _ ⟨w, hw, rfl⟩
  have h1 := hf.2 (mem_univ (y1 + w)) (mem_univ (y2 + w)) hs ht hst
  have e : s • (y1 + w) + t • (y2 + w) = s • y1 + t • y2 + w := by
    simp only [smul_eq_mul]
    calc s * (y1 + w) + t * (y2 + w) = s * y1 + t * y2 + (s + t) * w := by ring
      _ = s * y1 + t * y2 + w := by rw [hst, one_mul]
  rw [e] at h1
  have h2 : f (y1 + w) ≤ sSup ((fun w => f (y1 + w)) '' Icc a b) :=
    le_csSup (bddAbove_shift hfc y1 a b) ⟨w, hw, rfl⟩
  have h3 : f (y2 + w) ≤ sSup ((fun w => f (y2 + w)) '' Icc a b) :=
    le_csSup (bddAbove_shift hfc y2 a b) ⟨w, hw, rfl⟩
  calc f (s • y1 + t • y2 + w) ≤ s • f (y1 + w) + t • f (y2 + w) := h1
    _ ≤ _ := by
      simp only [smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h2 hs, mul_le_mul_of_nonneg_left h3 ht]

lemma gFun_convex {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') : ConvexOn ℝ univ (gFun M k J') := by
  have hf : ConvexOn ℝ univ (fun s => M.h k s + J' s) := (hM.h_convex k).add hJ
  exact sup_convex hf (hM.wlo_le_whi k)


lemma inf_attain {g : ℝ → ℝ} (hg : Continuous g) (c : ℝ) {L U : ℝ} (hLU : L ≤ U) (x : ℝ) :
    ∃ u ∈ Icc L U, IsMinOn (fun u => c * u + g (x + u)) (Icc L U) u :=
  isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hLU)
    (((continuous_const.mul continuous_id).add
      (hg.comp (continuous_const.add continuous_id))).continuousOn)

lemma sInf_eq_of_isMinOn {φ : ℝ → ℝ} {S : Set ℝ} {u : ℝ} (hu : u ∈ S) (h : IsMinOn φ S u) :
    sInf (φ '' S) = φ u :=
  IsLeast.csInf_eq ⟨⟨u, hu, rfl⟩, by rintro _ ⟨v, hv, rfl⟩; exact h hv⟩

lemma bddBelow_img {g : ℝ → ℝ} (hg : Continuous g) (c : ℝ) (x L U : ℝ) :
    BddBelow ((fun u => c * u + g (x + u)) '' Icc L U) :=
  (isCompact_Icc.image ((continuous_const.mul continuous_id).add
      (hg.comp (continuous_const.add continuous_id)))).bddBelow

lemma bellman_convex {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hg : ConvexOn ℝ univ (gFun M k J')) : ConvexOn ℝ univ (bellman M k J') := by
  have hgc := cont_of_convex hg
  have hLU := hM.L_le_U k
  refine ⟨convex_univ, fun x1 _ x2 _ s t hs ht hst => ?_⟩
  obtain ⟨u1, hu1, hm1⟩ := inf_attain hgc (M.c k) hLU x1
  obtain ⟨u2, hu2, hm2⟩ := inf_attain hgc (M.c k) hLU x2
  have e1 : bellman M k J' x1 = M.c k * u1 + gFun M k J' (x1 + u1) :=
    sInf_eq_of_isMinOn hu1 hm1
  have e2 : bellman M k J' x2 = M.c k * u2 + gFun M k J' (x2 + u2) :=
    sInf_eq_of_isMinOn hu2 hm2
  have hu : s • u1 + t • u2 ∈ Icc (M.L k) (M.U k) := (convex_Icc _ _) hu1 hu2 hs ht hst
  have h1 : bellman M k J' (s • x1 + t • x2) ≤
      M.c k * (s • u1 + t • u2) + gFun M k J' (s • x1 + t • x2 + (s • u1 + t • u2)) :=
    csInf_le (bddBelow_img hgc _ _ _ _) ⟨_, hu, rfl⟩
  have h2 := hg.2 (mem_univ (x1 + u1)) (mem_univ (x2 + u2)) hs ht hst
  have e : s • (x1 + u1) + t • (x2 + u2) = s • x1 + t • x2 + (s • u1 + t • u2) := by
    simp only [smul_eq_mul]; ring
  rw [e] at h2
  rw [e1, e2]
  simp only [smul_eq_mul] at h1 h2 ⊢
  nlinarith [h1, h2, hst]

lemma h_bdd {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) : ∃ m, ∀ y, m ≤ M.h k y := by
  have hc := cont_of_convex (hM.h_convex k)
  obtain ⟨x, hx⟩ := hc.exists_forall_le (hM.h_coercive k)
  exact ⟨_, hx⟩

lemma gFun_ge {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') (y w : ℝ) (hw : w ∈ Icc (M.wlo k) (M.whi k)) :
    M.h k (y + w) + J' (y + w) ≤ gFun M k J' y := by
  have hf : ConvexOn ℝ univ (fun s => M.h k s + J' s) := (hM.h_convex k).add hJ
  exact le_csSup (bddAbove_shift (cont_of_convex hf) y _ _) ⟨w, hw, rfl⟩

lemma gFun_bdd {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') (m : ℝ) (hm : ∀ x, m ≤ J' x) :
    ∃ mg, ∀ y, mg ≤ gFun M k J' y := by
  obtain ⟨mh, hmh⟩ := h_bdd M hM k
  refine ⟨mh + m, fun y => ?_⟩
  have := gFun_ge M hM k hJ y (M.wlo k) (left_mem_Icc.2 (hM.wlo_le_whi k))
  linarith [hmh (y + M.wlo k), hm (y + M.wlo k)]

lemma bellman_bdd {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (_hg : ConvexOn ℝ univ (gFun M k J')) (mg : ℝ) (hmg : ∀ y, mg ≤ gFun M k J' y) :
    ∃ m, ∀ x, m ≤ bellman M k J' x := by
  refine ⟨M.c k * M.L k + mg, fun x => ?_⟩
  unfold bellman
  refine le_csInf ⟨M.c k * M.L k + gFun M k J' (x + M.L k), M.L k, left_mem_Icc.2 (hM.L_le_U k), rfl⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  nlinarith [mul_le_mul_of_nonneg_left hu.1 (hM.c_nonneg k), hmg (x + u)]

lemma Jstar_ge_T {T : ℕ} (M : Model T) (j : ℕ) (hj : ¬ j < T) : Jstar M j = fun _ => 0 := by
  rw [Jstar, dif_neg hj]

lemma Jstar_lt_T {T : ℕ} (M : Model T) (j : ℕ) (hj : j < T) :
    Jstar M j = bellman M ⟨j, hj⟩ (Jstar M (j + 1)) := by
  rw [Jstar, dif_pos hj]

lemma good_all {T : ℕ} (M : Model T) (hM : M.Standing) :
    ∀ j : ℕ, ConvexOn ℝ univ (Jstar M j) ∧ ∃ m, ∀ x, m ≤ Jstar M j x := by
  have key : ∀ d j : ℕ, T ≤ j + d →
      ConvexOn ℝ univ (Jstar M j) ∧ ∃ m, ∀ x, m ≤ Jstar M j x := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [Jstar_ge_T M j (by omega)]
      exact ⟨convexOn_const 0 convex_univ, 0, fun _ => le_refl _⟩
    | succ d ih =>
      intro j hj
      by_cases hjT : j < T
      · obtain ⟨hc, m, hm⟩ := ih (j + 1) (by omega)
        rw [Jstar_lt_T M j hjT]
        have hg := gFun_convex M hM ⟨j, hjT⟩ hc
        obtain ⟨mg, hmg⟩ := gFun_bdd M hM ⟨j, hjT⟩ hc m hm
        exact ⟨bellman_convex M hM _ hg, bellman_bdd M hM _ hg mg hmg⟩
      · rw [Jstar_ge_T M j hjT]
        exact ⟨convexOn_const 0 convex_univ, 0, fun _ => le_refl _⟩
  exact fun j => key T j (by omega)


lemma proj_min {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) {L U u0 : ℝ} (hLU : L ≤ U)
    (h0 : ∀ u, ψ u0 ≤ ψ u) : IsMinOn ψ (Icc L U) (max L (min U u0)) := by
  intro u hu
  show ψ (max L (min U u0)) ≤ ψ u
  rcases lt_or_ge u0 L with h | h
  · have e : max L (min U u0) = L := by
      rw [min_eq_right (by linarith), max_eq_left h.le]
    rw [e]
    have := hψ.le_max_of_mem_Icc (mem_univ u0) (mem_univ u) (⟨h.le, hu.1⟩ : L ∈ Icc u0 u)
    exact this.trans (max_le (h0 u) le_rfl)
  · rcases le_or_gt u0 U with h' | h'
    · have e : max L (min U u0) = u0 := by rw [min_eq_right h', max_eq_right h]
      rw [e]; exact h0 u
    · have e : max L (min U u0) = U := by rw [min_eq_left h'.le, max_eq_right hLU]
      rw [e]
      have := hψ.le_max_of_mem_Icc (mem_univ u) (mem_univ u0) (⟨hu.2, h'.le⟩ : U ∈ Icc u u0)
      exact this.trans (max_le le_rfl (h0 u))

lemma clamp_mem {L U t : ℝ} (hLU : L ≤ U) : max L (min U t) ∈ Icc L U :=
  ⟨le_max_left _ _, max_le hLU (min_le_left _ _)⟩

lemma convex_psi {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) (c x : ℝ) :
    ConvexOn ℝ univ (fun u => c * u + g (x + u)) := by
  refine ⟨convex_univ, fun u1 _ u2 _ s t hs ht hst => ?_⟩
  have h2 := hg.2 (mem_univ (x + u1)) (mem_univ (x + u2)) hs ht hst
  have e : s • (x + u1) + t • (x + u2) = x + (s • u1 + t • u2) := by
    simp only [smul_eq_mul]
    calc s * (x + u1) + t * (x + u2) = (s + t) * x + (s * u1 + t * u2) := by ring
      _ = x + (s * u1 + t * u2) := by rw [hst, one_mul]
  rw [e] at h2
  simp only [smul_eq_mul] at h2 ⊢
  nlinarith [h2]

lemma clamp_opt {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) (c L U ystar : ℝ) (hLU : L ≤ U)
    (hy : IsMinOn (fun y => c * y + g y) univ ystar) (x : ℝ) :
    IsMinOn (fun u => c * u + g (x + u)) (Icc L U) (max L (min U (ystar - x))) := by
  apply proj_min (convex_psi hg c x) hLU
  intro u
  have h1 : c * ystar + g ystar ≤ c * (x + u) + g (x + u) := hy (mem_univ (x + u))
  have e : x + (ystar - x) = ystar := by ring
  show c * (ystar - x) + g (x + (ystar - x)) ≤ c * u + g (x + u)
  rw [e]
  nlinarith [h1]

lemma mono_of_no_min {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hlim : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hno : ¬ ∃ y, IsMinOn φ univ y) : Monotone φ := by
  intro p q hpq
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨r, hr1, hr2⟩ := ((hlim.eventually_gt_atTop (φ p)).and
    (Filter.eventually_gt_atTop q)).exists
  have hφc := cont_of_convex hφ
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (hpq.trans hr2.le))
    hφc.continuousOn
  apply hno
  refine ⟨m, fun y _ => ?_⟩
  show φ m ≤ φ y
  by_cases hyp : y < p
  · have h1 := hφ.le_max_of_mem_Icc (mem_univ y) (mem_univ q) (⟨hyp.le, hpq⟩ : p ∈ Icc y q)
    have h2 : φ p ≤ φ y := by
      rcases le_max_iff.1 h1 with h | h
      · exact h
      · exact absurd h (not_le.2 hlt)
    exact (hmin (⟨le_rfl, hpq.trans hr2.le⟩ : p ∈ Icc p r)).trans h2
  · by_cases hyr : r < y
    · have h1 := hφ.le_max_of_mem_Icc (mem_univ q) (mem_univ y) (⟨hr2.le, hyr.le⟩ : r ∈ Icc q y)
      have h2 : φ r ≤ φ y := by
        rcases le_max_iff.1 h1 with h | h
        · exact absurd h (not_le.2 (by linarith))
        · exact h
      exact (hmin (⟨hpq.trans hr2.le, le_rfl⟩ : r ∈ Icc p r)).trans h2
    · exact hmin (⟨not_lt.1 hyp, not_lt.1 hyr⟩ : y ∈ Icc p r)

lemma phi_tendsto {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) {J' : ℝ → ℝ}
    (hJ : ConvexOn ℝ univ J') (m : ℝ) (hm : ∀ x, m ≤ J' x) :
    Filter.Tendsto (fun y => M.c k * y + gFun M k J' y) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (M.h k) Filter.atTop Filter.atTop :=
    (hM.h_coercive k).mono_left atTop_le_cocompact
  have h2 : Filter.Tendsto (fun y => M.h k (y + M.wlo k) + m) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _
      (h1.comp (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id))
  refine Filter.tendsto_atTop_mono' _ ?_ h2
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
  have := gFun_ge M hM k hJ y (M.wlo k) (left_mem_Icc.2 (hM.wlo_le_whi k))
  nlinarith [mul_nonneg (hM.c_nonneg k) hy, hm (y + M.wlo k)]

lemma Jstar_fin {T : ℕ} (M : Model T) (k : Fin T) :
    Jstar M (k : ℕ) = bellman M k (Jstar M ((k : ℕ) + 1)) := by
  have := Jstar_lt_T M (k : ℕ) k.2
  simpa using this

theorem lemma_7_1 {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) :
    ConvexOn ℝ Set.univ (Jstar M k) ∧
    ConvexOn ℝ Set.univ (gFun M k (Jstar M ((k : ℕ) + 1))) ∧
    (∀ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (max (M.L k) (min (M.U k) (ystar - x))) ∧
          Jstar M k x = M.c k * max (M.L k) (min (M.U k) (ystar - x)) +
              gFun M k (Jstar M ((k : ℕ) + 1)) (x + max (M.L k) (min (M.U k) (ystar - x)))) ∧
    ((¬ ∃ ystar : ℝ,
        IsMinOn (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar) →
        ∀ x : ℝ,
          IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
              (Set.Icc (M.L k) (M.U k)) (M.L k) ∧
          Jstar M k x = M.c k * M.L k + gFun M k (Jstar M ((k : ℕ) + 1)) (x + M.L k)) := by
  obtain ⟨hc1, m1, hm1⟩ := good_all M hM ((k : ℕ) + 1)
  obtain ⟨hcK, _⟩ := good_all M hM (k : ℕ)
  have hg := gFun_convex M hM k hc1
  have hLU := hM.L_le_U k
  refine ⟨hcK, hg, ?_, ?_⟩
  · intro ystar hy x
    have hmin := clamp_opt hg (M.c k) (M.L k) (M.U k) ystar hLU hy x
    refine ⟨hmin, ?_⟩
    rw [Jstar_fin M k]
    exact sInf_eq_of_isMinOn (clamp_mem hLU) hmin
  · intro hno x
    have hφ : ConvexOn ℝ univ (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) := by
      simpa using convex_psi hg (M.c k) 0
    have hmono := mono_of_no_min hφ (phi_tendsto M hM k hc1 m1 hm1) hno
    have hmin : IsMinOn (fun u => M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u))
        (Icc (M.L k) (M.U k)) (M.L k) := by
      intro u hu
      show M.c k * M.L k + gFun M k (Jstar M ((k : ℕ) + 1)) (x + M.L k) ≤
        M.c k * u + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u)
      have h1 := hmono (show x + M.L k ≤ x + u by linarith [hu.1])
      simp only at h1
      nlinarith [h1]
    refine ⟨hmin, ?_⟩
    rw [Jstar_fin M k]
    exact sInf_eq_of_isMinOn (left_mem_Icc.2 hLU) hmin

end P172L71

namespace P172T

open AffinePolicyOpt.OneDim Set Finset P172Q P172Z

lemma prefix_sum (T j : ℕ) (hj : j ≤ T) (a v : ℕ → ℝ)
    (hv : ∀ l, v l = if l < j then 1 else 0) :
    ∑ l ∈ range T, a l * v l = As a j := by
  have h1 : ∀ l ∈ range T, a l * v l = if l < j then a l else 0 := by
    intro l _; rw [hv l]; split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  unfold As
  congr 1
  ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma prefix_sumB (T j : ℕ) (hj : j ≤ T) (b v : ℕ → ℝ)
    (hv : ∀ l, v l = if l < j then 1 else 0) :
    ∑ l ∈ range T, b l * v l = Bs b j :=
  prefix_sum T j hj b v hv

lemma prefix_box (T j : ℕ) (v : ℕ → ℝ) (hv : ∀ l, v l = if l < j then 1 else 0) :
    ∀ l, l < T → 0 ≤ v l ∧ v l ≤ 1 := by
  intro l _; rw [hv l]; split_ifs <;> norm_num

lemma sum_update_zero {T : ℕ} (k : Fin T) (f w : Fin T → ℝ) (v : ℝ) (hf : f k = 0) :
    ∑ t, f t * Function.update w k v t = ∑ t, f t * w t := by
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : t = k
  · subst h; simp [hf]
  · simp [h]

theorem stage_step {T : ℕ} (M : Model T) (hM : M.Standing) (k : Fin T) (α0 β0 : ℝ)
    (α β : Fin T → ℝ) (hs : ∀ t : Fin T, k ≤ t → α t = 0 ∧ β t = 0)
    (hval : IsGreatest ((fun w => (α0 + ∑ t, α t * w t) + Jstar M k (β0 + ∑ t, β t * w t)) ''
      {w | M.inBox w}) (JmM M)) :
    ∃ (a0 : ℝ) (a : Fin T → ℝ) (y0 : ℝ) (y : Fin T → ℝ),
      (∀ t, k ≤ t → a t = 0) ∧ (∀ t, k < t → y t = 0) ∧
      (∀ w, M.inBox w → M.L k ≤ a0 + ∑ t, a t * w t ∧ a0 + ∑ t, a t * w t ≤ M.U k) ∧
      (∀ w, M.inBox w →
        M.h k (β0 + ∑ t, β t * w t + (a0 + ∑ t, a t * w t) + w k) ≤ y0 + ∑ t, y t * w t) ∧
      IsGreatest ((fun w => (α0 + ∑ t, α t * w t) +
          (M.c k * (a0 + ∑ t, a t * w t) + (y0 + ∑ t, y t * w t)) +
          Jstar M ((k : ℕ) + 1) (β0 + ∑ t, β t * w t + (a0 + ∑ t, a t * w t) + w k)) ''
        {w | M.inBox w}) (JmM M) := by
  classical
  obtain ⟨_, hgc, h3, h4⟩ := P172L71.lemma_7_1 M hM k
  obtain ⟨hJ'c, _⟩ := P172L71.good_all M hM ((k : ℕ) + 1)
  have hLU := hM.L_le_U k
  -- the optimal policy law (clamp law, or the constant `L`)
  obtain ⟨u, hu, hlip, hJu⟩ : ∃ u : ℝ → ℝ, (∀ x, M.L k ≤ u x ∧ u x ≤ M.U k) ∧
      (∀ x t, 0 ≤ t → -t ≤ u (x + t) - u x ∧ u (x + t) - u x ≤ 0) ∧
      ∀ x, Jstar M k x = M.c k * u x + gFun M k (Jstar M ((k : ℕ) + 1)) (x + u x) := by
    by_cases hex : ∃ ystar, IsMinOn
        (fun y => M.c k * y + gFun M k (Jstar M ((k : ℕ) + 1)) y) Set.univ ystar
    · obtain ⟨ystar, hy⟩ := hex
      refine ⟨fun x => max (M.L k) (min (M.U k) (ystar - x)),
        fun x => ⟨(P172L71.clamp_mem hLU).1, (P172L71.clamp_mem hLU).2⟩, ?_,
        fun x => (h3 ystar hy x).2⟩
      intro x t ht
      show -t ≤ max (M.L k) (min (M.U k) (ystar - (x + t))) - max (M.L k) (min (M.U k) (ystar - x)) ∧
        max (M.L k) (min (M.U k) (ystar - (x + t))) - max (M.L k) (min (M.U k) (ystar - x)) ≤ 0
      have hB : max (M.L k) (min (M.U k) (ystar - (x + t))) ≤
          max (M.L k) (min (M.U k) (ystar - x)) :=
        max_le_max le_rfl (min_le_min le_rfl (by linarith))
      have hA : max (M.L k) (min (M.U k) (ystar - x)) ≤
          max (M.L k) (min (M.U k) (ystar - (x + t))) + t := by
        refine max_le (by linarith [le_max_left (M.L k) (min (M.U k) (ystar - (x + t)))]) ?_
        rcases le_total (M.U k) (ystar - (x + t)) with h | h
        · rw [min_eq_left h]
          linarith [le_max_right (M.L k) (M.U k), min_le_left (M.U k) (ystar - x)]
        · rw [min_eq_right h]
          linarith [le_max_right (M.L k) (ystar - (x + t)), min_le_right (M.U k) (ystar - x)]
      constructor <;> linarith
    · refine ⟨fun _ => M.L k, fun _ => ⟨le_rfl, hLU⟩, fun x t ht => ?_, fun x => (h4 hex x).2⟩
      show -t ≤ M.L k - M.L k ∧ M.L k - M.L k ≤ 0
      constructor <;> linarith
  -- q-step: normalize, build the policy on the cube, pull back
  obtain ⟨a, b, C1, C2, s, hW, hs01, hsv, hdec, hpull⟩ :=
    P172S.s1 T M.wlo M.whi α β (fun t => hM.wlo_le_whi t)
  obtain ⟨q0, q, hqz, hq⟩ := P172N.nq_step T a b hW (α0 + C1) (β0 + C2) (M.c k) (M.L k) (M.U k)
    u hu hlip (gFun M k (Jstar M ((k : ℕ) + 1))) hgc (JmM M) (by
      intro j hj
      obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, ∀ l, v l = if l < j then 1 else 0 := ⟨_, fun _ => rfl⟩
      obtain ⟨w, hwb, hwa, hwb'⟩ := hdec v (prefix_box T j v hv)
      rw [prefix_sum T j hj a v hv] at hwa
      rw [prefix_sumB T j hj b v hv] at hwb'
      have h1 : α0 + ∑ t, α t * w t + Jstar M k (β0 + ∑ t, β t * w t) ≤ JmM M :=
        hval.2 ⟨w, hwb, rfl⟩
      rw [hJu, hwa, hwb', ← add_assoc β0 C2] at h1
      linarith)
  obtain ⟨c0, cf, hcf0, hcf⟩ := hpull q0 q (fun l hl _ hb => hqz l hl hb)
  have hcfk : ∀ t, k ≤ t → cf t = 0 := fun t ht => hcf0 t (hs t ht).1 (hs t ht).2
  have hqb : ∀ w, M.inBox w → M.L k ≤ c0 + ∑ t, cf t * w t ∧ c0 + ∑ t, cf t * w t ≤ M.U k := by
    intro w hw
    rw [hcf w]
    exact (hq (s w) (hs01 w hw)).1
  have hqv : ∀ w, M.inBox w → α0 + ∑ t, α t * w t + M.c k * (c0 + ∑ t, cf t * w t) +
      gFun M k (Jstar M ((k : ℕ) + 1)) (β0 + ∑ t, β t * w t + (c0 + ∑ t, cf t * w t)) ≤ JmM M := by
    intro w hw
    have h1 := (hq (s w) (hs01 w hw)).2
    obtain ⟨ea, eb⟩ := hsv w hw
    rw [hcf w, ea, eb, ← add_assoc β0 C2]
    linarith
  -- z-step data
  obtain ⟨α1, hα1⟩ : ∃ α1 : Fin T → ℝ, ∀ t, α1 t = α t + M.c k * cf t := ⟨_, fun _ => rfl⟩
  obtain ⟨β1, hβ1⟩ : ∃ β1 : Fin T → ℝ, ∀ t, β1 t = β t + cf t + (if t = k then 1 else 0) :=
    ⟨_, fun _ => rfl⟩
  have hsumα1 : ∀ w : Fin T → ℝ,
      ∑ t, α1 t * w t = ∑ t, α t * w t + M.c k * ∑ t, cf t * w t := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hα1]; ring
  have hsumβ1 : ∀ w : Fin T → ℝ,
      ∑ t, β1 t * w t = ∑ t, β t * w t + ∑ t, cf t * w t + w k := by
    intro w
    have e : ∀ t, β1 t * w t = β t * w t + cf t * w t + (if t = k then w t else 0) := by
      intro t; rw [hβ1]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq']
    simp
  obtain ⟨a2, b2, D1, D2, s2, hW2, hs2, hsv2, hdec2, hpull2⟩ :=
    P172S.s1 T M.wlo M.whi α1 β1 (fun t => hM.wlo_le_whi t)
  have eX : ∀ w, M.inBox w → β0 + c0 + D2 + ∑ l ∈ range T, b2 l * s2 w l =
      β0 + ∑ t, β t * w t + (c0 + ∑ t, cf t * w t) + w k := by
    intro w hw
    have := (hsv2 w hw).2
    rw [hsumβ1] at this
    linarith
  have eA : ∀ w, M.inBox w → α0 + M.c k * c0 + D1 + ∑ l ∈ range T, a2 l * s2 w l =
      α0 + ∑ t, α t * w t + M.c k * (c0 + ∑ t, cf t * w t) := by
    intro w hw
    have := (hsv2 w hw).1
    rw [hsumα1] at this
    linear_combination (-1 : ℝ) * this
  obtain ⟨z0, z, hzz, hz⟩ := P172N.nz_step T a2 b2 hW2 (α0 + M.c k * c0 + D1) (β0 + c0 + D2)
    (M.h k) (Jstar M ((k : ℕ) + 1)) (hM.h_convex k) hJ'c (JmM M) (by
      intro j hj
      obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, ∀ l, v l = if l < j then 1 else 0 := ⟨_, fun _ => rfl⟩
      obtain ⟨w, hwb, hwa, hwb'⟩ := hdec2 v (prefix_box T j v hv)
      rw [prefix_sum T j hj a2 v hv, hsumα1] at hwa
      rw [prefix_sumB T j hj b2 v hv, hsumβ1] at hwb'
      have h1 := hqv w hwb
      have h2 := P172L71.gFun_ge M hM k hJ'c
        (β0 + ∑ t, β t * w t + (c0 + ∑ t, cf t * w t)) (w k) (hwb k)
      have e1 : β0 + c0 + D2 + Bs b2 j = β0 + ∑ t, β t * w t + (c0 + ∑ t, cf t * w t) + w k := by
        linarith
      have e2 : α0 + M.c k * c0 + D1 + As a2 j =
          α0 + ∑ t, α t * w t + M.c k * (c0 + ∑ t, cf t * w t) := by
        linear_combination (-1 : ℝ) * hwa
      rw [e1, e2]
      linarith)
  obtain ⟨y0, y, hy0, hy⟩ := hpull2 z0 z (fun l hl ha hb => hzz l hl ha hb)
  have hyk : ∀ t, k < t → y t = 0 := by
    intro t ht
    have h0 := hs t ht.le
    have hc := hcfk t ht.le
    refine hy0 t ?_ ?_
    · rw [hα1, h0.1, hc]; ring
    · rw [hβ1, h0.2, hc, if_neg ht.ne']; ring
  have hdom : ∀ w, M.inBox w →
      M.h k (β0 + ∑ t, β t * w t + (c0 + ∑ t, cf t * w t) + w k) ≤ y0 + ∑ t, y t * w t := by
    intro w hw
    have h1 := (hz (s2 w) (hs2 w hw)).1
    rw [eX w hw] at h1
    rw [hy w]; exact h1
  have hub : ∀ w, M.inBox w → (α0 + ∑ t, α t * w t) +
      (M.c k * (c0 + ∑ t, cf t * w t) + (y0 + ∑ t, y t * w t)) +
      Jstar M ((k : ℕ) + 1) (β0 + ∑ t, β t * w t + (c0 + ∑ t, cf t * w t) + w k) ≤ JmM M := by
    intro w hw
    have h2 := (hz (s2 w) (hs2 w hw)).2
    rw [eX w hw] at h2
    rw [hy w]
    linarith [eA w hw]
  refine ⟨c0, cf, y0, y, hcfk, hyk, hqb, hdom, ⟨?_, ?_⟩⟩
  · obtain ⟨w0, hw0, hv0⟩ := hval.1
    have hv0' : α0 + ∑ t, α t * w0 t + Jstar M k (β0 + ∑ t, β t * w0 t) = JmM M := hv0
    have hp := hqb w0 hw0
    have hJle : Jstar M k (β0 + ∑ t, β t * w0 t) ≤ M.c k * (c0 + ∑ t, cf t * w0 t) +
        gFun M k (Jstar M ((k : ℕ) + 1)) (β0 + ∑ t, β t * w0 t + (c0 + ∑ t, cf t * w0 t)) := by
      rw [P172L71.Jstar_fin M k]
      exact csInf_le (P172L71.bddBelow_img (P172L71.cont_of_convex hgc) _ _ _ _)
        ⟨c0 + ∑ t, cf t * w0 t, ⟨hp.1, hp.2⟩, rfl⟩
    have hfc : Continuous (fun x => M.h k x + Jstar M ((k : ℕ) + 1) x) :=
      P172L71.cont_of_convex ((hM.h_convex k).add hJ'c)
    obtain ⟨ws, hws, hsup⟩ := P172L71.sup_attain hfc (hM.wlo_le_whi k)
      (β0 + ∑ t, β t * w0 t + (c0 + ∑ t, cf t * w0 t))
    have hgeq : gFun M k (Jstar M ((k : ℕ) + 1))
        (β0 + ∑ t, β t * w0 t + (c0 + ∑ t, cf t * w0 t)) =
        M.h k (β0 + ∑ t, β t * w0 t + (c0 + ∑ t, cf t * w0 t) + ws) +
          Jstar M ((k : ℕ) + 1) (β0 + ∑ t, β t * w0 t + (c0 + ∑ t, cf t * w0 t) + ws) := hsup
    have hw1 : M.inBox (Function.update w0 k ws) := by
      intro t
      by_cases h : t = k
      · subst h; simpa using hws
      · simpa [Function.update_apply, h] using hw0 t
    refine ⟨Function.update w0 k ws, hw1, le_antisymm (hub _ hw1) ?_⟩
    have hd := hdom _ hw1
    show JmM M ≤ (α0 + ∑ t, α t * Function.update w0 k ws t) +
      (M.c k * (c0 + ∑ t, cf t * Function.update w0 k ws t) +
        (y0 + ∑ t, y t * Function.update w0 k ws t)) +
      Jstar M ((k : ℕ) + 1) (β0 + ∑ t, β t * Function.update w0 k ws t +
        (c0 + ∑ t, cf t * Function.update w0 k ws t) + Function.update w0 k ws k)
    simp only [sum_update_zero k α w0 ws (hs k le_rfl).1, sum_update_zero k β w0 ws (hs k le_rfl).2,
      sum_update_zero k cf w0 ws (hcfk k le_rfl), Function.update_self] at hd ⊢
    linarith
  · rintro _ ⟨w, hw, rfl⟩
    exact hub w hw

end P172T



namespace R172ae934

open AffinePolicyOpt.OneDim

/-- The child `stage_step` (one stage of §4 / Algorithm 1), for a fixed model `M`. -/
def StageStep {T : ℕ} (M : Model T) : Prop :=
  ∀ (k : Fin T) (α0 β0 : ℝ) (α β : Fin T → ℝ), (∀ t : Fin T, k ≤ t → α t = 0 ∧ β t = 0) →
    IsGreatest ((fun w => (α0 + ∑ t, α t * w t) + Jstar M k (β0 + ∑ t, β t * w t)) ''
      {w | M.inBox w}) (JmM M) →
    ∃ (a0 : ℝ) (a : Fin T → ℝ) (y0 : ℝ) (y : Fin T → ℝ),
      (∀ t, k ≤ t → a t = 0) ∧ (∀ t, k < t → y t = 0) ∧
      (∀ w, M.inBox w → M.L k ≤ a0 + ∑ t, a t * w t ∧ a0 + ∑ t, a t * w t ≤ M.U k) ∧
      (∀ w, M.inBox w →
        M.h k (β0 + ∑ t, β t * w t + (a0 + ∑ t, a t * w t) + w k) ≤ y0 + ∑ t, y t * w t) ∧
      IsGreatest ((fun w => (α0 + ∑ t, α t * w t) +
          (M.c k * (a0 + ∑ t, a t * w t) + (y0 + ∑ t, y t * w t)) +
          Jstar M ((k : ℕ) + 1) (β0 + ∑ t, β t * w t + (a0 + ∑ t, a t * w t) + w k)) ''
        {w | M.inBox w}) (JmM M)

/-- The three clauses (12), (13), (14) of Theorem 3.1 at stage `k`. -/
def Good {T : ℕ} (M : Model T) (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (z0 : Fin T → ℝ)
    (z : Fin T → Fin T → ℝ) (k : Fin T) : Prop :=
  (∀ w, M.inBox w → M.L k ≤ qEval q0 q k w ∧ qEval q0 q k w ≤ M.U k) ∧
  (∀ w, M.inBox w → M.h k (M.xAff q0 q k w) ≤ zEval z0 z k w) ∧
  IsGreatest
    ((fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
          (M.c t * qEval q0 q t w + zEval z0 z t w)) +
        Jstar M ((k : ℕ) + 1) (M.xAff q0 q k w)) '' {w | M.inBox w})
    (JmM M)

/-- Cumulative cost over stages `t < j`. -/
noncomputable def Cum {T : ℕ} (M : Model T) (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ)
    (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ) (j : ℕ) (w : Fin T → ℝ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < j), (M.c t * qEval q0 q t w + zEval z0 z t w)

/-- State after stages `t < j`. -/
noncomputable def Xs {T : ℕ} (M : Model T) (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ)
    (j : ℕ) (w : Fin T → ℝ) : ℝ :=
  M.x1 + ∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < j), (qEval q0 q t w + w t)

theorem qEval_eq {T : ℕ} (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (k : Fin T) (w : Fin T → ℝ) :
    qEval q0 q k w = q0 k + ∑ t, (if t < k then q k t else 0) * w t := by
  unfold qEval
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> simp

theorem zEval_eq {T : ℕ} (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ) (k : Fin T) (w : Fin T → ℝ) :
    zEval z0 z k w = z0 k + ∑ t, (if t ≤ k then z k t else 0) * w t := by
  unfold zEval
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> simp

theorem sum_aff {T : ℕ} (S : Finset (Fin T)) (A : Fin T → ℝ) (B : Fin T → Fin T → ℝ)
    (w : Fin T → ℝ) :
    ∑ s ∈ S, (A s + ∑ t, B s t * w t) = ∑ s ∈ S, A s + ∑ t, (∑ s ∈ S, B s t) * w t := by
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp [Finset.sum_mul]

theorem cum_aff {T : ℕ} (M : Model T) (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ)
    (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ) (j : ℕ) :
    ∃ (α0 : ℝ) (α : Fin T → ℝ), (∀ t : Fin T, j ≤ (t : ℕ) → α t = 0) ∧
      ∀ w, Cum M q0 q z0 z j w = α0 + ∑ t, α t * w t := by
  set S := Finset.univ.filter (fun t : Fin T => (t : ℕ) < j) with hS
  refine ⟨∑ s ∈ S, (M.c s * q0 s + z0 s),
    fun t => ∑ s ∈ S, (M.c s * (if t < s then q s t else 0) + (if t ≤ s then z s t else 0)),
    ?_, ?_⟩
  · intro t ht
    refine Finset.sum_eq_zero (fun s hs => ?_)
    have hs' : (s : ℕ) < j := (Finset.mem_filter.mp hs).2
    have h1 : ¬ t < s := by rw [Fin.lt_def]; omega
    have h2 : ¬ t ≤ s := by rw [Fin.le_iff_val_le_val]; omega
    simp [h1, h2]
  · intro w
    unfold Cum
    rw [← hS, ← sum_aff]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [qEval_eq, zEval_eq]
    simp only [mul_add, Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]
    ring

theorem xs_aff {T : ℕ} (M : Model T) (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (j : ℕ) :
    ∃ (β0 : ℝ) (β : Fin T → ℝ), (∀ t : Fin T, j ≤ (t : ℕ) → β t = 0) ∧
      ∀ w, Xs M q0 q j w = β0 + ∑ t, β t * w t := by
  set S := Finset.univ.filter (fun t : Fin T => (t : ℕ) < j) with hS
  refine ⟨M.x1 + ∑ s ∈ S, q0 s,
    fun t => ∑ s ∈ S, ((if t < s then q s t else 0) + (if t = s then 1 else 0)), ?_, ?_⟩
  · intro t ht
    refine Finset.sum_eq_zero (fun s hs => ?_)
    have hs' : (s : ℕ) < j := (Finset.mem_filter.mp hs).2
    have h1 : ¬ t < s := by rw [Fin.lt_def]; omega
    have h2 : t ≠ s := by intro h; rw [h] at ht; omega
    simp [h1, h2]
  · intro w
    unfold Xs
    rw [← hS, add_assoc, ← sum_aff]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [qEval_eq]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem filter_succ {T : ℕ} (k : Fin T) :
    Finset.univ.filter (fun t : Fin T => (t : ℕ) < (k : ℕ) + 1) =
      insert k (Finset.univ.filter (fun t : Fin T => (t : ℕ) < (k : ℕ))) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem filter_le {T : ℕ} (k : Fin T) :
    Finset.univ.filter (· ≤ k) = Finset.univ.filter (fun t : Fin T => (t : ℕ) < (k : ℕ) + 1) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
  omega

theorem sum_succ {T : ℕ} (k : Fin T) (f : Fin T → ℝ) :
    ∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < (k : ℕ) + 1), f t =
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < (k : ℕ)), f t + f k := by
  rw [filter_succ, Finset.sum_insert (by simp), add_comm]

/-- `Good` at stage `s` only reads the stage data at indices `t ≤ s`. -/
theorem good_congr {T : ℕ} (M : Model T) (q0 q0' : Fin T → ℝ) (q q' : Fin T → Fin T → ℝ)
    (z0 z0' : Fin T → ℝ) (z z' : Fin T → Fin T → ℝ) (s : Fin T)
    (hq : ∀ t, t ≤ s → ∀ w, qEval q0' q' t w = qEval q0 q t w)
    (hz : ∀ t, t ≤ s → ∀ w, zEval z0' z' t w = zEval z0 z t w) :
    Good M q0' q' z0' z' s ↔ Good M q0 q z0 z s := by
  have hx : ∀ w, M.xAff q0' q' s w = M.xAff q0 q s w := by
    intro w
    unfold Model.xAff
    congr 1
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [hq t (Finset.mem_filter.mp ht).2 w]
  have hc : ∀ w, ∑ t ∈ Finset.univ.filter (· ≤ s), (M.c t * qEval q0' q' t w + zEval z0' z' t w)
      = ∑ t ∈ Finset.univ.filter (· ≤ s), (M.c t * qEval q0 q t w + zEval z0 z t w) := by
    intro w
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [hq t (Finset.mem_filter.mp ht).2 w, hz t (Finset.mem_filter.mp ht).2 w]
  unfold Good
  simp only [hx, hc, hq s le_rfl, hz s le_rfl]

theorem key {T : ℕ} (M : Model T) (hM : M.Standing) (hstep : StageStep M) :
    ∀ j : ℕ, j ≤ T → ∃ (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (z0 : Fin T → ℝ)
      (z : Fin T → Fin T → ℝ), (∀ k : Fin T, (k : ℕ) < j → Good M q0 q z0 z k) ∧
      IsGreatest ((fun w => Cum M q0 q z0 z j w + Jstar M j (Xs M q0 q j w)) '' {w | M.inBox w})
        (JmM M) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, 0, 0, 0, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_⟩
    · refine ⟨M.wlo, fun t => ⟨le_rfl, hM.wlo_le_whi t⟩, ?_⟩
      simp [Cum, Xs, JmM]
    · rintro _ ⟨w, _, rfl⟩
      simp [Cum, Xs, JmM]
  | succ j ih =>
    intro hj
    obtain ⟨q0, q, z0, z, hgood, hval⟩ := ih (by omega)
    set k : Fin T := ⟨j, by omega⟩ with hk
    have hkj : (k : ℕ) = j := rfl
    obtain ⟨α0, α, hαs, hα⟩ := cum_aff M q0 q z0 z j
    obtain ⟨β0, β, hβs, hβ⟩ := xs_aff M q0 q j
    have hval' : IsGreatest ((fun w => (α0 + ∑ t, α t * w t) + Jstar M k (β0 + ∑ t, β t * w t)) ''
        {w | M.inBox w}) (JmM M) := by
      have hf : (fun w => (α0 + ∑ t, α t * w t) + Jstar M k (β0 + ∑ t, β t * w t)) =
          (fun w => Cum M q0 q z0 z j w + Jstar M j (Xs M q0 q j w)) := by
        funext w; rw [hα w, hβ w]
      rw [hf]; exact hval
    obtain ⟨a0, a, y0, y, ha, hy, h12, h13, h14⟩ :=
      hstep k α0 β0 α β (fun t ht => ⟨hαs t ht, hβs t ht⟩) hval'
    set q0' := Function.update q0 k a0
    set q' := Function.update q k a
    set z0' := Function.update z0 k y0
    set z' := Function.update z k y
    have hqne : ∀ s, s ≠ k → ∀ w, qEval q0' q' s w = qEval q0 q s w := by
      intro s hs w
      simp [qEval, q0', q', Function.update_of_ne hs]
    have hzne : ∀ s, s ≠ k → ∀ w, zEval z0' z' s w = zEval z0 z s w := by
      intro s hs w
      simp [zEval, z0', z', Function.update_of_ne hs]
    have hqk : ∀ w, qEval q0' q' k w = a0 + ∑ t, a t * w t := by
      intro w
      rw [qEval_eq]
      simp only [q0', q', Function.update_self]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs with h
      · rfl
      · rw [ha t (not_lt.mp h)]
    have hzk : ∀ w, zEval z0' z' k w = y0 + ∑ t, y t * w t := by
      intro w
      rw [zEval_eq]
      simp only [z0', z', Function.update_self]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs with h
      · rfl
      · rw [hy t (not_le.mp h)]
    have hlt : ∀ s : Fin T, (s : ℕ) < j → s ≠ k := by
      intro s hs h; rw [h] at hs; omega
    have hcum : ∀ w, Cum M q0' q' z0' z' j w = Cum M q0 q z0 z j w := by
      intro w
      unfold Cum
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have := hlt s (Finset.mem_filter.mp hs).2
      rw [hqne s this, hzne s this]
    have hxs : ∀ w, Xs M q0' q' j w = Xs M q0 q j w := by
      intro w
      unfold Xs
      congr 1
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [hqne s (hlt s (Finset.mem_filter.mp hs).2)]
    -- the new state and cumulative cost after stage k
    have hxk : ∀ w, M.xAff q0' q' k w =
        β0 + ∑ t, β t * w t + (a0 + ∑ t, a t * w t) + w k := by
      intro w
      have : M.xAff q0' q' k w = Xs M q0' q' j w + (qEval q0' q' k w + w k) := by
        unfold Model.xAff Xs
        rw [filter_le, sum_succ, hkj, add_assoc]
      rw [this, hxs, hβ, hqk]; ring
    have hck : ∀ w, ∑ t ∈ Finset.univ.filter (· ≤ k),
        (M.c t * qEval q0' q' t w + zEval z0' z' t w) =
        (α0 + ∑ t, α t * w t) + (M.c k * (a0 + ∑ t, a t * w t) + (y0 + ∑ t, y t * w t)) := by
      intro w
      rw [filter_le, sum_succ, hkj]
      have : ∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < j),
          (M.c t * qEval q0' q' t w + zEval z0' z' t w) = Cum M q0' q' z0' z' j w := rfl
      rw [this, hcum, hα, hqk, hzk]
    have h14' : IsGreatest
        ((fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
            (M.c t * qEval q0' q' t w + zEval z0' z' t w)) +
          Jstar M ((k : ℕ) + 1) (M.xAff q0' q' k w)) '' {w | M.inBox w}) (JmM M) := by
      have hf : (fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
            (M.c t * qEval q0' q' t w + zEval z0' z' t w)) +
          Jstar M ((k : ℕ) + 1) (M.xAff q0' q' k w)) =
          (fun w => (α0 + ∑ t, α t * w t) +
            (M.c k * (a0 + ∑ t, a t * w t) + (y0 + ∑ t, y t * w t)) +
            Jstar M ((k : ℕ) + 1) (β0 + ∑ t, β t * w t + (a0 + ∑ t, a t * w t) + w k)) := by
        funext w; rw [hck, hxk]
      rw [hf]; exact h14
    refine ⟨q0', q', z0', z', ?_, ?_⟩
    · intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
      · have hsk : s < k := by rw [Fin.lt_def]; omega
        rw [good_congr M q0 q0' q q' z0 z0' z z' s
          (fun t ht w => hqne t (ne_of_lt (lt_of_le_of_lt ht hsk)) w)
          (fun t ht w => hzne t (ne_of_lt (lt_of_le_of_lt ht hsk)) w)]
        exact hgood s hs
      · have hsk : s = k := Fin.ext (by rw [hs])
        subst hsk
        refine ⟨fun w hw => ?_, fun w hw => ?_, h14'⟩
        · rw [hqk]; exact h12 w hw
        · rw [hxk, hzk]; exact h13 w hw
    · have hf : (fun w => Cum M q0' q' z0' z' (j + 1) w + Jstar M (j + 1) (Xs M q0' q' (j + 1) w)) =
          (fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
            (M.c t * qEval q0' q' t w + zEval z0' z' t w)) +
          Jstar M ((k : ℕ) + 1) (M.xAff q0' q' k w)) := by
        funext w
        unfold Cum Xs Model.xAff
        rw [filter_le, hkj]
      rw [hf]; exact h14'

/-- Theorem 3.1 from the child `stage_step`. -/
theorem theorem_3_1_of_step {T : ℕ} (M : Model T) (hM : M.Standing) (hstep : StageStep M) :
    ∃ (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ),
      ∀ k : Fin T,
        (∀ w, M.inBox w → M.L k ≤ qEval q0 q k w ∧ qEval q0 q k w ≤ M.U k) ∧
        (∀ w, M.inBox w → M.h k (M.xAff q0 q k w) ≤ zEval z0 z k w) ∧
        IsGreatest
          ((fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
                (M.c t * qEval q0 q t w + zEval z0 z t w)) +
              Jstar M ((k : ℕ) + 1) (M.xAff q0 q k w)) '' {w | M.inBox w})
          (JmM M) := by
  obtain ⟨q0, q, z0, z, hg, _⟩ := key M hM hstep T le_rfl
  exact ⟨q0, q, z0, z, fun k => hg k k.isLt⟩

end R172ae934


open AffinePolicyOpt.OneDim in
theorem solution {T : ℕ} (M : Model T) (hM : M.Standing) :
    ∃ (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ),
      ∀ k : Fin T,
        (∀ w, M.inBox w → M.L k ≤ qEval q0 q k w ∧ qEval q0 q k w ≤ M.U k) ∧
        (∀ w, M.inBox w → M.h k (M.xAff q0 q k w) ≤ zEval z0 z k w) ∧
        IsGreatest
          ((fun w => (∑ t ∈ Finset.univ.filter (· ≤ k),
                (M.c t * qEval q0 q t w + zEval z0 z t w)) +
              Jstar M ((k : ℕ) + 1) (M.xAff q0 q k w)) '' {w | M.inBox w})
          (JmM M) := by
  exact R172ae934.theorem_3_1_of_step M hM
    (fun k α0 β0 α β hs hv => P172T.stage_step M hM k α0 β0 α β hs hv)
