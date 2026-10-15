-- Prove2me | solution 1 for AVRideHail.MonopolyCapacity.proposition8_optimal_capacity
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-14T19:59:09.220722+00:00
-- url     : https://prove2.me/submissions/9dcade0b-f57d-4449-a403-6ef3b8d1dffa

import Definitions.Def_AVRideHail_MonopolyCapacity_Model
namespace AVRideHail.MonopolyCapacity

open AVRideHail.PureHV

lemma avcap_aTilde_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) : 0 < aTilde P := by
  unfold aTilde
  have h1 : 0 < P.r ^ (1 / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) :=
    mul_pos (Real.rpow_pos_of_pos hr0 _) (Real.rpow_pos_of_pos ha _)
  have h2 : 0 < P.r ^ (-P.r / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) :=
    mul_pos (Real.rpow_pos_of_pos hr0 _) (Real.rpow_pos_of_pos ha _)
  linarith

lemma avcap_cont (P : MarketParams) (hr0 : 0 < P.r) : Continuous (nMin P) := by
  unfold nMin
  have : Continuous fun d : ℝ => d ^ (1 / (P.r + 1)) :=
    Real.continuous_rpow_const (by positivity)
  fun_prop

lemma avcap_zero (P : MarketParams) (hr0 : 0 < P.r) : nMin P 0 = 0 := by
  unfold nMin
  rw [Real.zero_rpow (by positivity)]
  ring

lemma avcap_smono (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2) :
    StrictMonoOn (nMin P) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold nMin
  have h1 : x ^ (1 / (P.r + 1)) ≤ y ^ (1 / (P.r + 1)) :=
    Real.rpow_le_rpow hx hxy.le (by positivity)
  have h2 := avcap_aTilde_pos P ha hr0
  have h3 : aTilde P * x ^ (1 / (P.r + 1)) ≤ aTilde P * y ^ (1 / (P.r + 1)) :=
    mul_le_mul_of_nonneg_left h1 h2.le
  have h4 : P.t2 * x < P.t2 * y := mul_lt_mul_of_pos_left hxy ht2
  linarith

lemma avcap_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (x : ℝ) (hx : 0 < x) : 0 < nMin P x := by
  have := avcap_smono P ha hr0 ht2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
  rwa [avcap_zero P hr0] at this

lemma avcap_dBar (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (n : ℝ) (hn : 0 ≤ n) : 0 ≤ dBar P n ∧ nMin P (dBar P n) = n := by
  have hex : ∃ a ∈ Set.Ici (0:ℝ), nMin P a = n := by
    have h0le : (0:ℝ) ≤ n / P.t2 := div_nonneg hn ht2.le
    have hup : n ≤ nMin P (n / P.t2) := by
      unfold nMin
      have : 0 ≤ aTilde P * (n / P.t2) ^ (1 / (P.r + 1)) :=
        mul_nonneg (avcap_aTilde_pos P ha hr0).le (Real.rpow_nonneg h0le _)
      have h2 : P.t2 * (n / P.t2) = n := by field_simp
      linarith
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc h0le
      (avcap_cont P hr0).continuousOn ⟨by rw [avcap_zero P hr0]; exact hn, hup⟩
    exact ⟨c, hc1.1, hc2⟩
  have := Function.invFunOn_pos hex
  exact ⟨this.1, this.2⟩

lemma avcap_hv (P : MarketParams) (halpha : P.alpha = 0) (d : ℝ) :
    hvCost P d = P.w0 * nMin P d := by
  unfold hvCost wage; rw [halpha]; ring

lemma avcap_rev_nonpos (P : MarketParams) (hV : 0 < P.V) (ht2 : 0 < P.t2) (m x : ℝ)
    (hm : 0 < m) (hx : 0 ≤ x) (hmx : m ≤ x) : revenue P m x ≤ 0 := by
  unfold revenue priceFn
  have : 1 - x / m ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hm]; linarith
  have : P.V * (1 - x / m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hV.le this
  have : x * (P.V * (1 - x / m)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx this
  exact mul_nonpos_of_nonpos_of_nonneg this ht2.le

/-- Above the maximal stable equilibrium, revenue is strictly below HV cost. -/
lemma avcap_above (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (hV : 0 < P.V) (halpha : P.alpha = 0) (hw0 : 0 < P.w0) (m : ℝ) (hm : 0 < m) (d : ℝ)
    (hd : IsMaxStableEq P m d) : ∀ x, d < x → revenue P m x < hvCost P x := by
  intro x hdx
  by_contra hcon
  push Not at hcon
  have hd0 : 0 ≤ d := hd.1.1.1
  have hx0 : 0 < x := lt_of_le_of_lt hd0 hdx
  set φ : ℝ → ℝ := fun y => revenue P m y - hvCost P y with hφ
  have hφc : Continuous φ := by
    have := avcap_cont P hr0
    simp only [hφ, revenue, priceFn, hvCost, wage]
    fun_prop
  have hxm : x < m := by
    by_contra h
    push Not at h
    have h1 := avcap_rev_nonpos P hV ht2 m x hm hx0.le h
    have h2 := avcap_pos P ha hr0 ht2 x hx0
    rw [avcap_hv P halpha] at hcon
    nlinarith
  have hφm : φ m < 0 := by
    simp only [hφ]
    have h1 : revenue P m m = 0 := by
      unfold revenue priceFn; rw [div_self hm.ne']; ring
    rw [h1, avcap_hv P halpha]
    have := avcap_pos P ha hr0 ht2 m hm
    nlinarith
  have hφx : 0 ≤ φ x := by simp only [hφ]; linarith
  set S : Set ℝ := Set.Icc x m ∩ φ ⁻¹' {0} with hS
  have hScomp : IsCompact S := isCompact_Icc.inter_right (isClosed_singleton.preimage hφc)
  have hSne : S.Nonempty := by
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hxm.le hφc.continuousOn
      (show (0:ℝ) ∈ Set.Icc (φ m) (φ x) from ⟨hφm.le, hφx⟩)
    exact ⟨c, hc1, hc2⟩
  obtain ⟨e, he, hemax⟩ := hScomp.exists_isGreatest hSne
  have heq : IsEquilibrium P m e := by
    refine ⟨by linarith [he.1.1], he.1.2, ?_⟩
    have := he.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hφ] at this
    linarith
  have hst : IsStable P m e := by
    rintro ⟨ε, hε, hεe, hem, _, h2⟩
    have hpos : 0 < φ (e + ε) := by simp only [hφ]; linarith
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hem hφc.continuousOn
      (show (0:ℝ) ∈ Set.Icc (φ m) (φ (e + ε)) from ⟨hφm.le, hpos.le⟩)
    have hcS : c ∈ S := ⟨⟨by linarith [he.1.1, hc1.1], hc1.2⟩, hc2⟩
    have := hemax hcS
    linarith [hc1.1]
  have := hd.2 ⟨heq, hst⟩
  linarith [he.1.1]

lemma avcap_half (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (hV : 0 < P.V) (halpha : P.alpha = 0) (hw0 : 0 < P.w0) (m : ℝ) (hm : 0 < m) (d : ℝ)
    (hd : IsMaxStableEq P m d) (hl : LooseMarket P m) : m / 2 ≤ d := by
  by_contra h
  push Not at h
  have := avcap_above P ha hr0 ht2 hV halpha hw0 m hm d hd (m / 2) h
  unfold LooseMarket at hl
  linarith

lemma avcap_rev_anti (P : MarketParams) (hV : 0 < P.V) (ht2 : 0 < P.t2) (m d x : ℝ)
    (hm : 0 < m) (hd : m / 2 ≤ d) (hdx : d ≤ x) : revenue P m x ≤ revenue P m d := by
  unfold revenue priceFn
  have key : 0 ≤ (x - d) * (x + d - m) := mul_nonneg (by linarith) (by linarith)
  have h : d * (P.V * (1 - d / m)) * P.t2 - x * (P.V * (1 - x / m)) * P.t2
      = P.V * P.t2 / m * ((x - d) * (x + d - m)) := by
    field_simp; ring
  have : 0 ≤ P.V * P.t2 / m * ((x - d) * (x + d - m)) :=
    mul_nonneg (by positivity) key
  linarith

lemma avcap_rev_mono_m (P : MarketParams) (hV : 0 < P.V) (ht2 : 0 < P.t2) (m m' d : ℝ)
    (hm : 0 < m) (hmm : m ≤ m') (hd : 0 ≤ d) : revenue P m d ≤ revenue P m' d := by
  unfold revenue priceFn
  have h1 : d / m' ≤ d / m := div_le_div_of_nonneg_left hd hm hmm
  have h2 : P.V * (1 - d / m) ≤ P.V * (1 - d / m') :=
    mul_le_mul_of_nonneg_left (by linarith) hV.le
  have h3 : d * (P.V * (1 - d / m)) ≤ d * (P.V * (1 - d / m')) :=
    mul_le_mul_of_nonneg_left h2 hd
  exact mul_le_mul_of_nonneg_right h3 ht2.le

lemma avcap_value (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r) (ht2 : 0 < P.t2)
    (hV : 0 < P.V) (halpha : P.alpha = 0) (cv : ℝ) (hcv : 0 < cv) (hw : cv < P.w0)
    (m : ℝ) (hm : 0 < m) (d : ℝ) (hd : IsMaxStableEq P m d) (hhalf : m / 2 ≤ d)
    (N : ℝ) (hN : 0 ≤ N) :
    monoValue P cv m d N = (P.w0 - cv) * min N (nMin P d) := by
  have hdpos : 0 < d := by linarith
  have hns : 0 < nMin P d := avcap_pos P ha hr0 ht2 d hdpos
  have hrev : revenue P m d = P.w0 * nMin P d := by
    rw [← avcap_hv P halpha]; exact hd.1.1.2.2
  have hsm := avcap_smono P ha hr0 ht2
  unfold monoValue
  apply IsGreatest.csSup_eq
  constructor
  · by_cases hNs : N < nMin P d
    · refine ⟨N, ⟨hN, le_rfl⟩, ?_⟩
      simp only [piC, if_pos hNs, min_eq_left hNs.le]
    · push Not at hNs
      refine ⟨nMin P d, ⟨hns.le, hNs⟩, ?_⟩
      obtain ⟨hb0, hb⟩ := avcap_dBar P ha hr0 ht2 (nMin P d) hns.le
      have hbd : dBar P (nMin P d) = d :=
        hsm.injOn (Set.mem_Ici.mpr hb0) (Set.mem_Ici.mpr hdpos.le) hb
      simp only [piC, lt_irrefl, if_false, hbd, min_eq_right hNs]
      unfold uBar
      have : priceFn P m d * (d * P.t2 / nMin P d) = revenue P m d / nMin P d := by
        unfold revenue; field_simp
      rw [this, hrev]
      field_simp
  · rintro _ ⟨n, ⟨hn0, hnN⟩, rfl⟩
    simp only [piC]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left (le_min hnN h.le) (by linarith)
    · push Not at h
      have hnpos : 0 < n := lt_of_lt_of_le hns h
      obtain ⟨he0, he⟩ := avcap_dBar P ha hr0 ht2 n hn0
      set e := dBar P n with he_def
      have hde : d ≤ e := by
        by_contra hlt
        push Not at hlt
        have := hsm (Set.mem_Ici.mpr he0) (Set.mem_Ici.mpr hdpos.le) hlt
        rw [he] at this
        linarith
      have hre := avcap_rev_anti P hV ht2 m d e hm hhalf hde
      rw [min_eq_right (le_trans h hnN)]
      have hval : (priceFn P m e * uBar P e - cv) * n = revenue P m e - cv * n := by
        unfold uBar revenue
        rw [he]
        field_simp
      rw [hval]
      nlinarith

theorem proposition8_optimal_capacity (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (halpha : P.alpha = 0)
    (cv cf : ℝ) (hcv : 0 < cv) (hcf : 0 < cf) (hA1 : cv + cf < P.w0)
    (I : ℕ) (hI : 0 < I) (prob : Fin I → ℝ) (hprob : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1)
    (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, AVRideHail.PureHV.LooseMarket P (m i))
    (dstar : Fin I → ℝ) (hdstar : ∀ i, AVRideHail.PureHV.IsMaxStableEq P (m i) (dstar i))
    (K : Fin I) (hK : IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < cf / (P.w0 - cv)} K) :
    IsMaxOn (monoProfit P cv cf prob m dstar) (Set.Ici 0) (AVRideHail.PureHV.nMin P (dstar K)) := by
  have hw0 : 0 < P.w0 := by linarith
  have hc : 0 < P.w0 - cv := by linarith
  have hhalf : ∀ i, m i / 2 ≤ dstar i := fun i =>
    avcap_half P ha hr0 ht2 hV halpha hw0 (m i) (hmpos i) (dstar i) (hdstar i) (hloose i)
  have hdpos : ∀ i, 0 < dstar i := fun i => by linarith [hhalf i, hmpos i]
  set ns : Fin I → ℝ := fun i => nMin P (dstar i) with hns_def
  have hnspos : ∀ i, 0 < ns i := fun i => avcap_pos P ha hr0 ht2 _ (hdpos i)
  have hdmono : ∀ i j, i ≤ j → dstar i ≤ dstar j := by
    intro i j hij
    rcases hij.lt_or_eq with hlt | heq
    · by_contra hcon
      push Not at hcon
      have h1 := avcap_above P ha hr0 ht2 hV halpha hw0 (m j) (hmpos j) (dstar j) (hdstar j)
        (dstar i) hcon
      have h2 := avcap_rev_mono_m P hV ht2 (m i) (m j) (dstar i) (hmpos i) (hm hlt).le
        (hdpos i).le
      have h3 := (hdstar i).1.1.2.2
      linarith
    · rw [heq]
  have hnsmono : ∀ i j, i ≤ j → ns i ≤ ns j := fun i j hij =>
    (avcap_smono P ha hr0 ht2).monotoneOn (Set.mem_Ici.mpr (hdpos i).le)
      (Set.mem_Ici.mpr (hdpos j).le) (hdmono i j hij)
  have hval : ∀ N, 0 ≤ N → monoProfit P cv cf prob m dstar N
      = (P.w0 - cv) * ∑ i, prob i * min N (ns i) - cf * N := by
    intro N hN
    unfold monoProfit
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [avcap_value P ha hr0 ht2 hV halpha cv hcv (by linarith) (m i) (hmpos i) (dstar i)
      (hdstar i) (hhalf i) N hN]
    ring
  have hTsum : ∀ k : Fin I, ∑ j ∈ Finset.Ioi k, prob j = ∑ j, if k < j then prob j else 0 := by
    intro k
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  intro N hN
  simp only [Set.mem_Ici] at hN
  show monoProfit P cv cf prob m dstar N ≤ monoProfit P cv cf prob m dstar (ns K)
  rw [hval N hN, hval (ns K) (hnspos K).le]
  set c := P.w0 - cv with hc_def
  have hdiff : ∑ i, prob i * min N (ns i) - ∑ i, prob i * min (ns K) (ns i)
      = ∑ i, prob i * (min N (ns i) - min (ns K) (ns i)) := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring
  rcases le_or_gt (ns K) N with hNK | hNK
  · -- N ≥ ns K
    have hle : ∑ i, prob i * (min N (ns i) - min (ns K) (ns i))
        ≤ ∑ i, (if K < i then prob i else 0) * (N - ns K) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hKi
      · apply mul_le_mul_of_nonneg_left _ (hprob i)
        have := hnsmono K i hKi.le
        rw [min_eq_left this]
        linarith [min_le_left N (ns i)]
      · push Not at hKi
        have := hnsmono i K hKi
        rw [min_eq_right (le_trans this hNK), min_eq_right this]
        simp
    have hT : ∑ i, (if K < i then prob i else 0) * (N - ns K)
        = (∑ j ∈ Finset.Ioi K, prob j) * (N - ns K) := by
      rw [hTsum K, Finset.sum_mul]
    have hKT : c * ∑ j ∈ Finset.Ioi K, prob j < cf := by
      have := hK.1
      simp only [Set.mem_setOf_eq] at this
      rw [lt_div_iff₀ hc] at this
      linarith
    have h1 : c * ((∑ j ∈ Finset.Ioi K, prob j) * (N - ns K)) ≤ cf * (N - ns K) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKT.le (by linarith)
    have h2 := mul_le_mul_of_nonneg_left (hT ▸ hle) hc.le
    rw [← hdiff] at h2
    nlinarith
  · -- N < ns K
    have hle : ∑ i, prob i * (min N (ns i) - min (ns K) (ns i))
        ≤ ∑ i, (if K ≤ i then prob i else 0) * (N - ns K) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hKi
      · have := hnsmono K i hKi
        rw [min_eq_left (le_trans hNK.le this), min_eq_left this]
      · push Not at hKi
        have := hnsmono i K hKi.le
        rw [min_eq_right this, zero_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (hprob i) (by linarith [min_le_right N (ns i)])
    have hS : cf ≤ c * ∑ i, (if K ≤ i then prob i else 0) := by
      by_cases hK0 : K.val = 0
      · have : ∑ i, (if K ≤ i then prob i else 0) = 1 := by
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro i _
          rw [if_pos]
          rw [Fin.le_def]; omega
        rw [this]; linarith
      · set k' : Fin I := ⟨K.val - 1, by omega⟩ with hk'
        have hnot : ¬ (∑ j ∈ Finset.Ioi k', prob j < cf / c) := by
          intro h
          have := hK.2 h
          rw [Fin.le_def] at this
          simp [hk'] at this
          omega
        push Not at hnot
        rw [div_le_iff₀ hc, hTsum k'] at hnot
        have : ∑ j, (if k' < j then prob j else 0) = ∑ i, (if K ≤ i then prob i else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          have : (k' < j ↔ K ≤ j) := by
            rw [Fin.lt_def, Fin.le_def]; simp [hk']; omega
          simp only [this]
        rw [this] at hnot
        linarith
    have hT : ∑ i, (if K ≤ i then prob i else 0) * (N - ns K)
        = (∑ i, (if K ≤ i then prob i else 0)) * (N - ns K) := by
      rw [Finset.sum_mul]
    have h1 : c * ((∑ i, (if K ≤ i then prob i else 0)) * (N - ns K)) ≤ cf * (N - ns K) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonpos_right hS (by linarith)
    have h2 := mul_le_mul_of_nonneg_left (hT ▸ hle) hc.le
    rw [← hdiff] at h2
    nlinarith


-- Platform entry point: restates the target verbatim.
namespace AVRideHail.MonopolyCapacity

theorem _root_.solution (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (halpha : P.alpha = 0)
    (cv cf : ℝ) (hcv : 0 < cv) (hcf : 0 < cf) (hA1 : cv + cf < P.w0)
    (I : ℕ) (hI : 0 < I) (prob : Fin I → ℝ) (hprob : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1)
    (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, AVRideHail.PureHV.LooseMarket P (m i))
    (dstar : Fin I → ℝ) (hdstar : ∀ i, AVRideHail.PureHV.IsMaxStableEq P (m i) (dstar i))
    (K : Fin I) (hK : IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < cf / (P.w0 - cv)} K) :
    IsMaxOn (monoProfit P cv cf prob m dstar) (Set.Ici 0) (AVRideHail.PureHV.nMin P (dstar K)) := by
  apply @AVRideHail.MonopolyCapacity.proposition8_optimal_capacity <;> assumption

end AVRideHail.MonopolyCapacity
