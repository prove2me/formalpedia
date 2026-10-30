-- Prove2me | solution 1 for APrioriTSP.Sampling.bucket_feasible_samplingLP
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:21:42.240613+00:00
-- url     : https://prove2.me/submissions/27df5041-3359-4846-be46-6018d11784a8

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP
import Theorems.Thm_APrioriTSP_Sampling_lemma_13
import Theorems.Thm_APrioriTSP_Sampling_lemma_14
import Theorems.Thm_APrioriTSP_Sampling_proposition_12

open APrioriTSP.Sampling Finset

theorem APTSP_summable_lin_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℝ) :
    Summable (fun n : ℕ => r ^ n * (((n : ℝ) + 1) * L)) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ 1 * r ^ n + r ^ n) * L) := by
    apply Summable.mul_right
    apply Summable.add
    · exact summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith)
    · exact summable_geometric_of_lt_one hr0 hr1
  exact h1.congr (fun n => by ring)

theorem APTSP_tiling (h : ℕ) (g : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range (M + 1),
      ∑ j ∈ Finset.Icc (max 1 (i * (2 * h + 1) - h)) (i * (2 * h + 1) + h), g j =
        ∑ j ∈ Finset.Icc 1 (M * (2 * h + 1) + h), g j := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    obtain ⟨m, hm⟩ : ∃ m, m = k * (2 * h + 1) := ⟨_, rfl⟩
    have e1 : (k + 1) * (2 * h + 1) = m + (2 * h + 1) := by rw [hm]; ring
    rw [e1, ← hm]
    rw [← Finset.sum_union]
    · congr 1
      ext j; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega

theorem solution (α σ β : ℝ) (N : ℕ) (hβ : 0 < β) (hα : 0 ≤ α)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (b : ℕ) (hb : Odd b) (hbβ : β < b) (C : ℕ → ℝ)
    (hC : SamplingOPFeasible α σ (β / b) C) :
    SamplingLPFeasible α σ β N (bucket b C) (fun i j => min (bucket b C i) (bucket b C j)) := by
  obtain ⟨hC0, hCt, h8⟩ := hC
  have hbpos : (0 : ℝ) < b := lt_trans hβ hbβ
  set p : ℝ := β / (b : ℝ) with hp
  have hp0 : 0 < p := div_pos hβ hbpos
  have hp1 : p < 1 := by rw [hp, div_lt_one hbpos]; exact hbβ
  have hbp : (b : ℝ) * p = β := by rw [hp]; field_simp
  set B : ℕ → ℝ := bucket b C with hBdef
  have hB0 : ∀ i, 0 ≤ B i := by
    intro i; simp only [hBdef, bucket]; apply Finset.sum_nonneg; intro j hj
    exact hC0 j (le_trans (le_max_left _ _) (Finset.mem_Icc.1 hj).1)
  have hBt : ∀ i j, 1 ≤ i → 1 ≤ j → B (i + j) ≤ B i + B j := proposition_12 b hb C hCt
  have hBlin : ∀ i : ℕ, B i ≤ ((i : ℝ) + 1) * (B 0 + B 1) := by
    intro i
    induction i with
    | zero => simp; linarith [hB0 1]
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp; linarith [hB0 0, hB0 1]
      · have := hBt k 1 hk le_rfl
        push_cast
        nlinarith [hB0 0, hB0 1]
  have hClin : ∀ n : ℕ, C (n + 1) ≤ ((n : ℝ) + 1) * C 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have := hCt (k + 1) 1 (by omega) le_rfl
      push_cast
      linarith
  set L : ℝ := B 0 + B 1 with hL
  have hL0 : 0 ≤ L := add_nonneg (hB0 0) (hB0 1)
  set r : ℝ := Real.exp (-(σ * β)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; nlinarith
  have hexp1 : ∀ k : ℕ, Real.exp (-(((k : ℝ) - 1) * σ * β)) = Real.exp (σ * β) * r ^ k := by
    intro k; rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have hexp2 : ∀ i j : ℕ, Real.exp (-(((i : ℝ) + j - 1) * σ * β)) =
      Real.exp (σ * β) * r ^ i * r ^ j := by
    intro i j; rw [hr, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  -- summability of Σ e_k B_k
  set fE : ℕ → ℝ := fun k => Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k with hfE
  have hfE0 : ∀ k, 0 ≤ fE k := fun k => mul_nonneg (Real.exp_pos _).le (hB0 k)
  have hfEs : Summable fE := by
    apply Summable.of_nonneg_of_le hfE0 _
      ((APTSP_summable_lin_geom hr0 hr1 L).mul_left (Real.exp (σ * β)))
    intro k
    simp only [hfE]
    rw [hexp1]
    have := hBlin k
    have hrk : 0 ≤ r ^ k := pow_nonneg hr0 _
    have he : 0 ≤ Real.exp (σ * β) := (Real.exp_pos _).le
    calc Real.exp (σ * β) * r ^ k * B k ≤ Real.exp (σ * β) * r ^ k * (((k : ℝ) + 1) * L) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg he hrk)
      _ = _ := by ring
  -- summability of F on ℕ × ℕ
  set F : ℕ × ℕ → ℝ := fun q =>
    Real.exp (-(((q.1 : ℝ) + q.2 - 1) * σ * β)) * min (B q.1) (B q.2) with hFdef
  have hF0 : ∀ q, 0 ≤ F q := fun q =>
    mul_nonneg (Real.exp_pos _).le (le_min (hB0 _) (hB0 _))
  have hFs : Summable F := by
    have hprod := Summable.mul_of_nonneg
      ((APTSP_summable_lin_geom hr0 hr1 L).mul_left (Real.exp (σ * β)))
      (summable_geometric_of_lt_one hr0 hr1)
      (fun n => by
        have := pow_nonneg hr0 n
        have : 0 ≤ ((n : ℝ) + 1) * L := mul_nonneg (by positivity) hL0
        simp only [Pi.zero_apply]; positivity)
      (fun n => by simp only [Pi.zero_apply]; exact pow_nonneg hr0 n)
    apply Summable.of_nonneg_of_le hF0 _ hprod
    intro q
    simp only [hFdef]
    rw [hexp2]
    have h1 : min (B q.1) (B q.2) ≤ ((q.1 : ℝ) + 1) * L := le_trans (min_le_left _ _) (hBlin _)
    have he : 0 ≤ Real.exp (σ * β) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (σ * β) * r ^ q.1 * r ^ q.2 :=
      mul_nonneg (mul_nonneg he (pow_nonneg hr0 _)) (pow_nonneg hr0 _)
    calc Real.exp (σ * β) * r ^ q.1 * r ^ q.2 * min (B q.1) (B q.2)
        ≤ Real.exp (σ * β) * r ^ q.1 * r ^ q.2 * (((q.1 : ℝ) + 1) * L) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  -- the two parts of (8)
  set s : ℝ := 1 - σ * p with hs
  have hs0 : 0 ≤ s := by rw [hs]; nlinarith
  have hs1 : s < 1 := by rw [hs]; nlinarith
  set A : ℕ → ℝ := fun k => s ^ k * C (k + 1) with hA
  set Mn : ℕ → ℝ := fun k => s ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) with hMn
  have hA0 : ∀ k, 0 ≤ A k := fun k => mul_nonneg (pow_nonneg hs0 _) (hC0 _ (by omega))
  have hAs : Summable A := by
    apply Summable.of_nonneg_of_le hA0 _ (APTSP_summable_lin_geom hs0 hs1 (C 1))
    intro k
    exact mul_le_mul_of_nonneg_left (hClin k) (pow_nonneg hs0 _)
  have h8' : 1 / σ ^ 2 ≤ ∑' k : ℕ, (α * A k + 2 * p * Mn k) := by
    have : (fun k : ℕ => (1 - σ * p) ^ k *
        (α * C (k + 1) + 2 * p * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)))) =
        fun k => α * A k + 2 * p * Mn k := by
      funext k; simp only [hA, hMn, hs]; ring
    rw [this] at h8; exact h8
  have hsumAM : Summable (fun k => α * A k + 2 * p * Mn k) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h8'
    have : 0 < 1 / σ ^ 2 := by positivity
    linarith
  have hMs : Summable Mn := by
    have := (hsumAM.sub (hAs.mul_left α)).mul_left (1 / (2 * p))
    refine this.congr (fun k => ?_)
    field_simp
    ring
  have hsplit8 : ∑' k : ℕ, (α * A k + 2 * p * Mn k) = α * ∑' k, A k + 2 * p * ∑' k, Mn k := by
    rw [Summable.tsum_add (hAs.mul_left α) (hMs.mul_left (2 * p)), tsum_mul_left, tsum_mul_left]
  -- Lemma 13
  have h13 := lemma_13 σ p hσ0 hσ1 hp0 hp1 b hb C hC0 hCt
  have hexpr : ∀ x : ℝ, x * σ * (b : ℝ) * p = x * σ * β := by
    intro x; rw [mul_assoc (x * σ), hbp]
  simp_rw [hexpr] at h13
  have hT : ∑' i : ℕ, ∑' j : ℕ, Real.exp (-(((i : ℝ) + j - 1) * σ * β)) *
      min (bucket b C i) (bucket b C j) = ∑' q : ℕ × ℕ, F q := by
    rw [hFs.tsum_prod' (fun i => hFs.prod_factor i)]
  rw [hT] at h13
  have hMbound : 2 * p * ∑' k, Mn k ≤ 2 * β * ∑' q : ℕ × ℕ, F q := by
    have : 2 * p * ∑' k, Mn k ≤ 2 * p * ((b : ℝ) * ∑' q : ℕ × ℕ, F q) :=
      mul_le_mul_of_nonneg_left h13 (by positivity)
    calc 2 * p * ∑' k, Mn k ≤ 2 * p * ((b : ℝ) * ∑' q : ℕ × ℕ, F q) := this
      _ = 2 * ((b : ℝ) * p) * ∑' q : ℕ × ℕ, F q := by ring
      _ = _ := by rw [hbp]
  -- first part: regrouping into buckets
  obtain ⟨h, rfl⟩ := hb
  have hhalf : (2 * h + 1 - 1) / 2 = h := by omega
  have hAbound : ∑' k, A k ≤ ∑' k, fE k := by
    apply Real.tsum_le_of_sum_range_le hA0
    intro n
    have hn1 : ∑ k ∈ range n, A k ≤ ∑ k ∈ range (n * (2 * h + 1) + h), A k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk; simp at hk ⊢; nlinarith
      · intro k _ _; exact hA0 k
    have hn2 : ∑ k ∈ range (n * (2 * h + 1) + h), A k =
        ∑ j ∈ Finset.Icc 1 (n * (2 * h + 1) + h), s ^ (j - 1) * C j := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr (by congr 1) _
      intro k _
      simp only [hA]
      congr 2 <;> omega
    rw [← APTSP_tiling h] at hn2
    have hn3 : ∑ i ∈ range (n + 1), ∑ j ∈ Finset.Icc (max 1 (i * (2 * h + 1) - h))
        (i * (2 * h + 1) + h), s ^ (j - 1) * C j ≤ ∑ i ∈ range (n + 1), fE i := by
      apply Finset.sum_le_sum
      intro i _
      simp only [hfE, hBdef, bucket, hhalf, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_Icc] at hj
      apply mul_le_mul_of_nonneg_right _ (hC0 j (le_trans (le_max_left _ _) hj.1))
      have hj1 : 1 ≤ j := le_trans (le_max_left _ _) hj.1
      have hj2 : i * (2 * h + 1) ≤ j + h := by
        have := le_trans (le_max_right _ _) hj.1
        omega
      have hjR : ((i : ℝ) * (2 * h + 1)) ≤ (j : ℝ) + h := by exact_mod_cast hj2
      -- s^(j-1) ≤ exp(-σp)^(j-1) = exp(-σp(j-1)) ≤ exp(-(i-1)σβ)
      have hs_le : s ≤ Real.exp (-(σ * p)) := by
        rw [hs]; have := Real.add_one_le_exp (-(σ * p)); linarith
      calc s ^ (j - 1) ≤ (Real.exp (-(σ * p))) ^ (j - 1) := pow_le_pow_left₀ hs0 hs_le _
        _ = Real.exp (-(σ * p) * ((j - 1 : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (-(((i : ℝ) - 1) * σ * β)) := by
          apply Real.exp_le_exp.2
          have hjc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj1]; simp
          rw [hjc, ← hbp]
          push_cast
          have hσp : 0 < σ * p := mul_pos hσ0 hp0
          nlinarith
    have hn4 : ∑ i ∈ range (n + 1), fE i ≤ ∑' k, fE k :=
      hfEs.sum_le_tsum _ (fun i _ => hfE0 i)
    linarith
  -- splitting the tails
  set tE : ℕ → ℝ := fun k => if N < k then Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k else 0
    with htE
  set tF : ℕ × ℕ → ℝ := fun q => if N < max q.1 q.2 then
    Real.exp (-(((q.1 : ℝ) + q.2 - 1) * σ * β)) * min (B q.1) (B q.2) else 0 with htF
  have hsplitE : ∑' k, fE k = ∑ k ∈ range (N + 1), fE k + ∑' k, tE k := by
    have htEs : Summable tE := by
      apply Summable.of_nonneg_of_le _ _ hfEs
      · intro k; simp only [htE]; split_ifs
        · exact hfE0 k
        · exact le_rfl
      · intro k; simp only [htE]; split_ifs
        · exact le_rfl
        · exact hfE0 k
    set hE : ℕ → ℝ := fun k => if N < k then 0 else fE k with hhE
    have hdec : ∀ k, fE k = hE k + tE k := by
      intro k; simp only [hhE, htE, hfE]; split_ifs <;> ring
    have hhEs : Summable hE := by
      refine (hfEs.sub htEs).congr (fun k => ?_); rw [hdec k]; ring
    rw [tsum_congr hdec, Summable.tsum_add hhEs htEs]
    congr 1
    rw [tsum_eq_sum (s := range (N + 1))]
    · apply Finset.sum_congr rfl
      intro k hk; simp at hk; simp only [hhE]; rw [if_neg (by omega)]
    · intro k hk; simp at hk; simp only [hhE]; rw [if_pos (by omega)]
  have hsplitF : ∑' q, F q = ∑ q ∈ range (N + 1) ×ˢ range (N + 1), F q + ∑' q, tF q := by
    have htFs : Summable tF := by
      apply Summable.of_nonneg_of_le _ _ hFs
      · intro q; simp only [htF]; split_ifs
        · exact hF0 q
        · exact le_rfl
      · intro q; simp only [htF]; split_ifs
        · exact le_rfl
        · exact hF0 q
    set hF' : ℕ × ℕ → ℝ := fun q => if N < max q.1 q.2 then 0 else F q with hhF
    have hdec : ∀ q, F q = hF' q + tF q := by
      intro q; simp only [hhF, htF, hFdef]; split_ifs <;> ring
    have hhFs : Summable hF' := by
      refine (hFs.sub htFs).congr (fun q => ?_); rw [hdec q]; ring
    rw [tsum_congr hdec, Summable.tsum_add hhFs htFs]
    congr 1
    rw [tsum_eq_sum (s := range (N + 1) ×ˢ range (N + 1))]
    · apply Finset.sum_congr rfl
      intro q hq; simp at hq; simp only [hhF]; rw [if_neg (by omega)]
    · intro q hq
      simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hq
      simp only [hhF]; rw [if_pos (by omega)]
  have h14 := lemma_14 α σ β hα hσ0 hβ N B hB0 hBt
  -- box sum bound
  have hbox : ∑ q ∈ range (N + 1) ×ˢ range (N + 1), F q ≤
      2 * ∑ j ∈ range (N + 1), ∑ i ∈ range (j + 1),
        Real.exp (-(((i : ℝ) + j - 1) * σ * β)) * min (B i) (B j) := by
    set R := range (N + 1) with hR
    set G : ℕ → ℕ → ℝ := fun i j => Real.exp (-(((i : ℝ) + j - 1) * σ * β)) * min (B i) (B j)
      with hG
    have hGsymm : ∀ i j, G i j = G j i := by
      intro i j; simp only [hG]; rw [min_comm]; ring_nf
    have hG0 : ∀ i j, 0 ≤ G i j := fun i j =>
      mul_nonneg (Real.exp_pos _).le (le_min (hB0 _) (hB0 _))
    rw [Finset.sum_product]
    have e1 : ∀ j ∈ R, ∑ i ∈ range (j + 1), G i j = ∑ i ∈ R, if i ≤ j then G i j else 0 := by
      intro j hj
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i; simp [hR] at hj ⊢; omega
    rw [Finset.sum_congr rfl e1]
    rw [Finset.sum_comm (s := R) (t := R) (f := fun j i => if i ≤ j then G i j else 0)]
    have e2 : ∑ i ∈ R, ∑ j ∈ R, G i j ≤ ∑ i ∈ R, ∑ j ∈ R, ((if i ≤ j then G i j else 0) +
        (if j ≤ i then G i j else 0)) := by
      apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
      by_cases hij : i ≤ j
      · rw [if_pos hij]; split_ifs <;> linarith [hG0 i j]
      · rw [if_neg hij, if_pos (by omega)]; simp
    have e3 : ∑ i ∈ R, ∑ j ∈ R, (if j ≤ i then G i j else 0) =
        ∑ i ∈ R, ∑ j ∈ R, (if i ≤ j then G i j else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      rw [hGsymm]
    simp only [Finset.sum_add_distrib] at e2
    rw [e3] at e2
    simp only [hG] at e2 ⊢
    linarith
  -- assemble
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmain : 1 / σ ^ 2 ≤ α * ∑' k, fE k + 2 * β * ∑' q, F q := by
      have := mul_le_mul_of_nonneg_left hAbound hα
      linarith
    rw [hsplitE, hsplitF] at hmain
    have h14' : α * ∑' k, tE k + 2 * β * ∑' q, tF q ≤
        delta1 β σ N * ∑ k ∈ range (N + 1), fE k + delta2 α β σ N * B 1 := h14
    have hb2 := mul_le_mul_of_nonneg_left hbox (by linarith : (0 : ℝ) ≤ 2 * β)
    show 1 / σ ^ 2 ≤ (α + delta1 β σ N) * ∑ k ∈ range (N + 1), fE k +
      delta2 α β σ N * B 1 + 4 * β * ∑ j ∈ range (N + 1), ∑ i ∈ range (j + 1),
        Real.exp (-(((i : ℝ) + j - 1) * σ * β)) * min (B i) (B j)
    nlinarith
  · intro i j hi _ hij; exact hBt i j hi (by omega)
  · intro i j _ _; exact min_le_left _ _
  · intro i j _ _; exact min_le_right _ _
  · intro i _; exact hB0 i
  · intro i j _ _; exact le_min (hB0 _) (hB0 _)
