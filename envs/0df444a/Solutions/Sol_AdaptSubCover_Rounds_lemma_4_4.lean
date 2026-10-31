-- Prove2me | solution 1 for AdaptSubCover.Rounds.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:18:43.477846+00:00
-- url     : https://prove2.me/submissions/931aa3c0-c93e-4e7f-a7e0-329297f1f7fb

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis
import Theorems.Thm_AdaptSubCover_Rounds_lemma_4_1

open AdaptSubCover.Rounds

namespace ASCL44

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem prob_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (ω : Fin m → U) :
    0 ≤ I.prob ω := Finset.prod_nonneg fun i _ => hp0 i (ω i)

theorem E_mono (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F G : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 < I.prob ω → F ω ≤ G ω) : I.E F ≤ I.E G := by
  unfold Instance.E
  apply Finset.sum_le_sum
  intro ω _
  rcases (prob_nonneg I hp0 ω).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (h ω hp) hp.le
  · rw [← hp]; simp

theorem E_sum {ι : Type} (I : Instance U m) (s : Finset ι) (F : ι → (Fin m → U) → ℝ) :
    I.E (fun ω => ∑ j ∈ s, F j ω) = ∑ j ∈ s, I.E (F j) := by
  unfold Instance.E
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem E_sub (I : Instance U m) (F G : (Fin m → U) → ℝ) :
    I.E (fun ω => F ω - G ω) = I.E F - I.E G := by
  unfold Instance.E
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ω _; ring

theorem E_add (I : Instance U m) (F G : (Fin m → U) → ℝ) :
    I.E (fun ω => F ω + G ω) = I.E F + I.E G := by
  unfold Instance.E
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ω _; ring

theorem ind_nonneg (p : Prop) {inst : Decidable p} : (0 : ℝ) ≤ if p then 1 else 0 := by
  split <;> norm_num

theorem P_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (A : (Fin m → U) → Prop) :
    0 ≤ I.P A := by
  unfold Instance.P Instance.E
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (prob_nonneg I hp0 ω) (@ind_nonneg _ (Classical.propDecidable _))

theorem ind_sum_le_one {ι : Type} (s : Finset ι) (A : ι → Prop) {inst : ∀ j, Decidable (A j)}
    (h : ∀ j ∈ s, ∀ j' ∈ s, A j → A j' → j = j') :
    ∑ j ∈ s, (if A j then (1 : ℝ) else 0) ≤ 1 := by
  by_cases hex : ∃ j ∈ s, A j
  · obtain ⟨j0, hj0, hA0⟩ := hex
    rw [Finset.sum_eq_single_of_mem j0 hj0 (fun j hj hne => if_neg (fun hA => hne (h j hj j0 hj0 hA hA0)))]
    simp [hA0]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun j hj => if_neg (hex j hj))]
    norm_num

/-- Scales are disjoint. -/
theorem scale_unique (x : ℝ) (j j' : ℕ)
    (h1 : (2⁻¹ : ℝ) ^ j / 2 < x) (h2 : x ≤ (2⁻¹ : ℝ) ^ j)
    (h1' : (2⁻¹ : ℝ) ^ j' / 2 < x) (h2' : x ≤ (2⁻¹ : ℝ) ^ j') : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (2⁻¹ : ℝ) ^ j' ≤ (2⁻¹ : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at this
    linarith
  · have : (2⁻¹ : ℝ) ^ j ≤ (2⁻¹ : ℝ) ^ (j' + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at this
    linarith

/-- Every value `F < Q` lies in some scale `j ≤ log Q`. -/
theorem scale_exists (Q F : ℕ) (hFQ : F < Q) :
    ∃ j : ℕ, j ≤ Nat.log 2 Q ∧ (2⁻¹ : ℝ) ^ j / 2 < ((Q : ℝ) - F) / Q ∧
        ((Q : ℝ) - F) / Q ≤ (2⁻¹ : ℝ) ^ j := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hinv : ∀ j : ℕ, (2⁻¹ : ℝ) ^ j = 1 / 2 ^ j := by intro j; rw [inv_pow, one_div]
  set d := Q - F with hd
  have hd1 : 1 ≤ d := by omega
  have hdQ : d ≤ Q := by omega
  set j := Nat.log 2 (Q / d)
  have hqd : Q / d ≠ 0 := by
    have : 1 ≤ Q / d := (Nat.one_le_div_iff (by omega)).mpr hdQ
    omega
  have h1 : 2 ^ j * d ≤ Q := by
    have := Nat.pow_log_le_self 2 hqd
    calc 2 ^ j * d ≤ Q / d * d := Nat.mul_le_mul_right _ this
      _ ≤ Q := Nat.div_mul_le_self Q d
  have h2 : Q < 2 ^ (j + 1) * d := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Q / d)
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp this
  have hdr : ((Q : ℝ) - F) = (d : ℝ) := by
    rw [hd, Nat.cast_sub hFQ.le]
  have h1r : (2 : ℝ) ^ j * d ≤ Q := by exact_mod_cast h1
  have h2r : (Q : ℝ) < 2 ^ (j + 1) * d := by exact_mod_cast h2
  refine ⟨j, ?_, ?_, ?_⟩
  · apply Nat.log_mono_right
    exact Nat.div_le_self Q d
  · rw [hdr, hinv, lt_div_iff₀ hQr]
    rw [pow_succ] at h2r
    rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith
  · rw [hdr, hinv, div_le_iff₀ hQr]
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ h2j]
    linarith

end ASCL44

open ASCL44 in
theorem solution {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (hτ : ∀ n : ℕ, (n : ℝ) ≠ I.tau z)
    (L : List (Fin m)) (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (π : AdaptivePolicy m U) (hπ : I.Feasible π)
    (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : 1 ≤ i)
    (t : ℝ) (ht1 : α * 2 ^ (i - 1) ≤ t) (ht2 : t < α * 2 ^ i) :
    I.goodSum π i z (I.prefixAt L t) ≥
      I.uPhase (I.tau z) α L i - 6 / 5 * I.uStar π i := by
  classical
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI'
  have hL' := hL
  obtain ⟨hnd, hLuniv, -⟩ := hL'
  set S := I.prefixAt L t with hSdef
  set X : (Fin m → U) → ℝ := fun ω => (I.costOf (I.NA (I.tau z) L ω) : ℝ) with hXdef
  set Y : (Fin m → U) → ℝ := fun ω => (I.costOf (π.run ω) : ℝ) with hYdef
  have ht0 : 0 ≤ t := le_trans (by positivity) ht1
  -- the prefix index
  set k := Nat.findGreatest (fun j => (I.cumCost L j : ℝ) ≤ t) L.length with hk
  have hpre : S = (L.take k).toFinset := rfl
  have hPk : (I.cumCost L k : ℝ) ≤ t := by
    have := Nat.findGreatest_spec (P := fun j => (I.cumCost L j : ℝ) ≤ t) (m := 0)
      (n := L.length) (Nat.zero_le _) (by simp [Instance.cumCost, ht0])
    exact this
  have hcum : ∀ j, (I.cumCost L j : ℝ) = ∑ e ∈ (L.take j).toFinset, (I.c e : ℝ) := by
    intro j
    unfold Instance.cumCost
    rw [List.sum_toFinset _ ((List.take_sublist j L).nodup hnd)]
    push_cast
    rw [List.map_map]
    rfl
  have hcostle : ∀ (h : History m U) (A : Finset (Fin m)), h.items ⊆ A →
      (I.costOf h : ℝ) ≤ ∑ e ∈ A, (I.c e : ℝ) := by
    intro h A hA
    unfold Instance.costOf; push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => by positivity)
  -- stopping by time t bounds the cost of NA by t
  have hstopcost : ∀ ω, I.NAStoppedBy (I.tau z) L t ω → X ω ≤ t := by
    intro ω hs
    have := hcostle _ (L.take k).toFinset hs
    rw [← hcum k] at this
    exact this.trans hPk
  have htot : ∀ ω, X ω ≤ I.cumCost L L.length := by
    intro ω
    rw [hcum, List.take_length, hLuniv]
    exact hcostle _ _ (Finset.subset_univ _)
  -- Step 1: non-good scales
  have hstep1 : ∀ j, ¬ I.Good π i j S →
      I.rStar π i j S ≤ 1 / 5 * I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω) := by
    intro j hng
    have hr0 : 0 ≤ I.rStar π i j S := P_nonneg I hp0 _
    have hp20 := P_nonneg I hp0 (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω)
    have hrE : I.rStar π i j S ≤ I.P (I.InScale j S) := by
      unfold Instance.rStar Instance.P
      apply E_mono I hp0
      intro ω _
      by_cases h : I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ I.InScale j S ω
      · rw [if_pos h, if_pos h.2.2]
      · rw [if_neg h]; exact ind_nonneg _
    have hEr : I.P (I.InScale j S) ≤
        I.rStar π i j S + I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω) := by
      unfold Instance.rStar Instance.P
      rw [← E_add]
      apply E_mono I hp0
      intro ω hω
      by_cases hE : I.InScale j S ω
      · rw [if_pos hE]
        by_cases hY : (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i
        · rw [if_pos ⟨hπ ω hω, hY, hE⟩]
          linarith [@ind_nonneg ((2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω) (Classical.propDecidable _)]
        · push Not at hY
          rw [if_pos (⟨hY.le, hE⟩ : (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω)]
          linarith [@ind_nonneg (I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            I.InScale j S ω) (Classical.propDecidable _)]
      · rw [if_neg hE]
        exact add_nonneg (ind_nonneg _) (ind_nonneg _)
    unfold Instance.Good at hng
    push Not at hng
    rcases (P_nonneg I hp0 (I.InScale j S)).lt_or_eq with hpos | hzero
    · rw [div_lt_iff₀ hpos] at hng
      linarith
    · rw [← hzero] at hrE
      linarith
  -- Step 2: the sum over all scales above δ
  have hstep2 : I.uPhase (I.tau z) α L i - I.uStar π i ≤
      ∑ j ∈ Finset.range z, I.rStar π i j S := by
    unfold Instance.uPhase Instance.uStar Instance.rStar Instance.P
    rw [← E_sub, ← E_sum]
    apply E_mono I hp0
    intro ω hω
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range z,
        @ite ℝ (I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ I.InScale j S ω)
          (Classical.propDecidable _) 1 0 :=
      Finset.sum_nonneg fun j _ => ind_nonneg _
    by_cases hu : α * 2 ^ i ≤ X ω
    · by_cases hus : (2 : ℝ) ^ i ≤ Y ω
      · rw [if_pos hu, if_pos hus, sub_self]
        exact Finset.sum_nonneg fun j _ => ind_nonneg _
      · rw [if_pos hu, if_neg hus]
        push Not at hus
        -- NA is not stopped by time t
        have hns : ¬ I.NAStoppedBy (I.tau z) L t ω := by
          intro hs; have := hstopcost ω hs; linarith
        have htl : t < (I.cumCost L L.length : ℝ) := by linarith [htot ω]
        have h41 := AdaptSubCover.Rounds.lemma_4_1 I hI hQ z hτ L hL t ht0 htl ω
        rw [h41] at hns
        push Not at hns
        obtain ⟨hnoscale, hneQ⟩ := hns
        have hFQ : I.f (S.image ω) < I.Q := by
          have : I.f (S.image ω) ≤ I.Q := hmon (Finset.subset_univ _)
          exact lt_of_le_of_ne this hneQ
        obtain ⟨j, hjlog, hj1, hj2⟩ := scale_exists I.Q (I.f (S.image ω)) hFQ
        have hjE : I.InScale j S ω := ⟨hjlog, hj1, hj2⟩
        have hjz : j < z := by
          by_contra hjz; push Not at hjz; exact hnoscale j hjz hjE
        have hterm : @ite ℝ (I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            I.InScale j S ω) (Classical.propDecidable _) 1 0 = 1 :=
          if_pos ⟨hπ ω hω, hus.le, hjE⟩
        have := Finset.single_le_sum (f := fun j => @ite ℝ (I.Covers (π.run ω) ∧
            (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ I.InScale j S ω) (Classical.propDecidable _) 1 0)
          (fun j _ => ind_nonneg _) (Finset.mem_range.mpr hjz)
        rw [hterm] at this
        linarith
    · rw [if_neg hu, zero_sub]
      refine le_trans ?_ (Finset.sum_nonneg fun j _ => ind_nonneg _)
      rw [neg_nonpos]
      exact ind_nonneg _
  -- Step 3: the OPT-tail mass over disjoint scales
  have hstep3 : ∀ B : Finset ℕ,
      ∑ j ∈ B, I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω) ≤ I.uStar π i := by
    intro B
    unfold Instance.uStar Instance.P
    rw [← E_sum]
    apply E_mono I hp0
    intro ω _
    by_cases hus : (2 : ℝ) ^ i ≤ Y ω
    · rw [if_pos hus]
      apply ind_sum_le_one
      intro j _ j' _ h h'
      exact scale_unique _ j j' h.2.2.1 h.2.2.2 h'.2.2.1 h'.2.2.2
    · rw [if_neg hus]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun h => hus h.1)
  -- combine
  unfold Instance.goodSum
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range z)
    (fun j => I.Good π i j S) (fun j => I.rStar π i j S)
  have hbad : ∑ j ∈ (Finset.range z).filter (fun j => ¬ I.Good π i j S), I.rStar π i j S ≤
      1 / 5 * I.uStar π i := by
    calc _ ≤ ∑ j ∈ (Finset.range z).filter (fun j => ¬ I.Good π i j S),
          1 / 5 * I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hstep1 j (Finset.mem_filter.mp hj).2
      _ = 1 / 5 * ∑ j ∈ (Finset.range z).filter (fun j => ¬ I.Good π i j S),
          I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ I.InScale j S ω) := by rw [Finset.mul_sum]
      _ ≤ 1 / 5 * I.uStar π i := by
          apply mul_le_mul_of_nonneg_left (hstep3 _) (by norm_num)
  linarith
