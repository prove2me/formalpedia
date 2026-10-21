-- Prove2me | solution 1 for AVRideHail.MonopolyCapacity.proposition7_optimal_fleet
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:58:24.784752+00:00
-- url     : https://prove2.me/submissions/af9e4b8b-626b-4602-b14b-e1090ef115b4

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

set_option autoImplicit false
open AVRideHail.PureHV AVRideHail.MonopolyCapacity

lemma av_aTilde_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) : 0 < aTilde P := by
  unfold aTilde
  have h1 : 0 ≤ P.r ^ (1 / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) :=
    mul_nonneg (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg ha.le _)
  have h2 : 0 < P.r ^ (-P.r / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) := by
    apply mul_pos _ (Real.rpow_pos_of_pos ha _)
    rcases hr0.lt_or_eq with h | h
    · exact Real.rpow_pos_of_pos h _
    · rw [← h]; simp
  linarith

lemma av_e_pos (P : MarketParams) (hr0 : 0 ≤ P.r) : 0 < 1 / (P.r + 1) :=
  div_pos one_pos (by linarith)

lemma av_nMin_cont (P : MarketParams) (hr0 : 0 ≤ P.r) : Continuous (nMin P) := by
  unfold nMin
  have : Continuous fun d : ℝ => d ^ (1 / (P.r + 1)) :=
    Real.continuous_rpow_const (le_of_lt (av_e_pos P hr0))
  fun_prop

lemma av_nMin_zero (P : MarketParams) (hr0 : 0 ≤ P.r) : nMin P 0 = 0 := by
  unfold nMin
  rw [Real.zero_rpow (ne_of_gt (av_e_pos P hr0))]
  simp

lemma av_nMin_sm (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) :
    StrictMonoOn (nMin P) (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold nMin
  have h1 : x ^ (1 / (P.r + 1)) < y ^ (1 / (P.r + 1)) :=
    Real.rpow_lt_rpow hx hxy (av_e_pos P hr0)
  have h2 := av_aTilde_pos P ha hr0
  nlinarith [mul_lt_mul_of_pos_left h1 h2, mul_lt_mul_of_pos_left hxy ht2]

lemma av_nMin_ge (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (d : ℝ) (hd : 0 ≤ d) :
    P.t2 * d ≤ nMin P d := by
  unfold nMin
  have h1 : 0 ≤ d ^ (1 / (P.r + 1)) := Real.rpow_nonneg hd _
  have h2 := av_aTilde_pos P ha hr0
  nlinarith [mul_nonneg h2.le h1]

lemma av_nMin_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) (d : ℝ)
    (hd : 0 < d) : 0 < nMin P d := by
  have := av_nMin_ge P ha hr0 d hd.le
  nlinarith [mul_pos ht2 hd]

lemma av_bij (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) :
    Set.BijOn (nMin P) (Set.Ici 0) (Set.Ici 0) := by
  have hsm := av_nMin_sm P ha hr0 ht2
  refine ⟨?_, hsm.injOn, ?_⟩
  · intro d hd
    have := av_nMin_ge P ha hr0 d hd
    have : 0 ≤ P.t2 * d := mul_nonneg ht2.le hd
    show 0 ≤ nMin P d
    linarith [av_nMin_ge P ha hr0 d hd]
  · intro y hy
    have hy0 : 0 ≤ y := hy
    have hle : (0:ℝ) ≤ y / P.t2 := by positivity
    have hivt := intermediate_value_Icc hle (av_nMin_cont P hr0).continuousOn
    have hmem : y ∈ Set.Icc (nMin P 0) (nMin P (y / P.t2)) := by
      rw [av_nMin_zero P hr0]
      refine ⟨hy0, ?_⟩
      have := av_nMin_ge P ha hr0 (y / P.t2) hle
      have e : P.t2 * (y / P.t2) = y := by field_simp
      linarith
    obtain ⟨d, hd, hdy⟩ := hivt hmem
    exact ⟨d, hd.1, hdy⟩

lemma av_dstar_ge (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2)
    (hw0 : 0 < P.w0) (halpha : P.alpha = 0) (m : ℝ) (hm : 0 < m) (hloose : LooseMarket P m)
    (dstar : ℝ) (hd : IsMaxStableEq P m dstar) : m / 2 ≤ dstar := by
  have hcost : ∀ d, hvCost P d = P.w0 * nMin P d := by
    intro d; unfold hvCost wage; rw [halpha]; ring
  set g : ℝ → ℝ := fun d => revenue P m d - hvCost P d with hg
  have hnc : Continuous (nMin P) := av_nMin_cont P hr0
  have hgc : Continuous g := by
    simp only [hg, revenue, priceFn, hcost]
    fun_prop
  have hg_half : 0 < g (m / 2) := by
    have := hloose
    unfold LooseMarket at this
    simp only [hg]; linarith
  have hg_m : g m < 0 := by
    simp only [hg, hcost, revenue, priceFn]
    rw [div_self hm.ne']
    have := av_nMin_pos P ha hr0 ht2 m hm
    nlinarith [mul_pos hw0 this]
  have hroot : ∃ x ∈ Set.Icc (m / 2) m, g x = 0 := by
    have := intermediate_value_Icc' (by linarith : m / 2 ≤ m) hgc.continuousOn
    exact this ⟨hg_m.le, hg_half.le⟩
  set Z := Set.Icc (m / 2) m ∩ {d | g d = 0} with hZ
  have hZc : IsCompact Z := isCompact_Icc.inter_right (isClosed_eq hgc continuous_const)
  have hZne : Z.Nonempty := by
    obtain ⟨x, hx, hx0⟩ := hroot
    exact ⟨x, hx, hx0⟩
  obtain ⟨d1, hd1⟩ := hZc.exists_isGreatest hZne
  have hd1m : d1 ∈ Set.Icc (m / 2) m := hd1.1.1
  have hd1g : g d1 = 0 := hd1.1.2
  have hneg : ∀ x ∈ Set.Ioc d1 m, g x < 0 := by
    intro x hx
    by_contra hnn
    push_neg at hnn
    have := intermediate_value_Icc' hx.2 hgc.continuousOn
    obtain ⟨y, hy, hgy⟩ := this ⟨hg_m.le, hnn⟩
    have hyZ : y ∈ Z := ⟨⟨by linarith [hd1m.1, hx.1, hy.1], hy.2⟩, hgy⟩
    have := hd1.2 hyZ
    linarith [hy.1, hx.1]
  have hmem : d1 ∈ {x | IsEquilibrium P m x ∧ IsStable P m x} := by
    refine ⟨⟨by linarith [hd1m.1], hd1m.2, ?_⟩, ?_⟩
    · simp only [hg] at hd1g; linarith
    · rintro ⟨ε, hε, hεd, hεm, hlt1, hlt2⟩
      have := hneg (d1 + ε) ⟨by linarith, hεm⟩
      simp only [hg] at this
      linarith
  have := hd.2 hmem
  linarith [hd1m.1]

lemma av_Psi_anti (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2)
    (hV : 0 < P.V) (m : ℝ) (hm : 0 < m) (cv : ℝ) (hcv : 0 < cv) (d1 d2 : ℝ) (h1 : m / 2 ≤ d1)
    (h12 : d1 < d2) :
    revenue P m d2 - cv * nMin P d2 < revenue P m d1 - cv * nMin P d1 := by
  have hd1 : 0 ≤ d1 := by linarith
  have hn := av_nMin_sm P ha hr0 ht2 hd1 (by simp only [Set.mem_Ici]; linarith) h12
  have hrev : revenue P m d2 - revenue P m d1 =
      P.V * P.t2 * (d2 - d1) * (1 - (d1 + d2) / m) := by
    unfold revenue priceFn
    field_simp
    ring
  have hneg : 1 - (d1 + d2) / m < 0 := by
    have : 1 < (d1 + d2) / m := by rw [lt_div_iff₀ hm]; linarith
    linarith
  have : P.V * P.t2 * (d2 - d1) * (1 - (d1 + d2) / m) < 0 :=
    mul_neg_of_pos_of_neg (by have := sub_pos.2 h12; positivity) hneg
  nlinarith [mul_pos hcv (sub_pos.2 hn)]

lemma av_dBar (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) (n : ℝ)
    (hn : 0 ≤ n) : 0 ≤ dBar P n ∧ nMin P (dBar P n) = n := by
  obtain ⟨d, hd, hdn⟩ := (av_bij P ha hr0 ht2).surjOn (show n ∈ Set.Ici (0:ℝ) from hn)
  exact Function.invFunOn_pos ⟨d, hd, hdn⟩

lemma av_Phi_anti (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2)
    (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : P.alpha = 0) (cv : ℝ) (hcv : 0 < cv) (m : ℝ)
    (hm : 0 < m) (hloose : LooseMarket P m) (dstar : ℝ) (hdstar : IsMaxStableEq P m dstar) :
    StrictAntiOn (fun n => priceFn P m (dBar P n) * dBar P n * P.t2 - cv * n)
      (Set.Ici (nMin P dstar)) := by
  have hd := av_dstar_ge P ha hr0 ht2 hw0 halpha m hm hloose dstar hdstar
  have hdpos : 0 < dstar := by linarith
  have hn0 : 0 < nMin P dstar := av_nMin_pos P ha hr0 ht2 dstar hdpos
  have hsm := av_nMin_sm P ha hr0 ht2
  intro x hx y hy hxy
  have hx' : nMin P dstar ≤ x := hx
  have hy' : nMin P dstar ≤ y := hy
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨hdx0, hdx⟩ := av_dBar P ha hr0 ht2 x hx0
  obtain ⟨hdy0, hdy⟩ := av_dBar P ha hr0 ht2 y hy0
  have hdxy : dBar P x < dBar P y := by
    refine (hsm.lt_iff_lt hdx0 hdy0).1 ?_
    rw [hdx, hdy]; exact hxy
  have hdxd : dstar ≤ dBar P x := by
    by_contra hlt
    push_neg at hlt
    have := hsm (show dBar P x ∈ Set.Ici (0:ℝ) from hdx0) (show dstar ∈ Set.Ici (0:ℝ) from hdpos.le)
      (by exact hlt)
    rw [hdx] at this
    linarith
  have e : ∀ n, 0 ≤ n → priceFn P m (dBar P n) * dBar P n * P.t2 - cv * n =
      revenue P m (dBar P n) - cv * nMin P (dBar P n) := by
    intro n hn
    rw [(av_dBar P ha hr0 ht2 n hn).2]
    unfold revenue; ring
  show priceFn P m (dBar P y) * dBar P y * P.t2 - cv * y <
    priceFn P m (dBar P x) * dBar P x * P.t2 - cv * x
  rw [e y hy0, e x hx0]
  exact av_Psi_anti P ha hr0 ht2 hV m hm cv hcv (dBar P x) (dBar P y) (by linarith) hdxy

lemma av_max (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2)
    (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : P.alpha = 0) (cv : ℝ) (hcv : 0 < cv)
    (hwc : cv < P.w0) (m : ℝ) (hm : 0 < m) (hloose : LooseMarket P m) (dstar : ℝ)
    (hdstar : IsMaxStableEq P m dstar) (N : ℝ) (hN : 0 ≤ N) :
    (∀ n ∈ Set.Icc 0 N, piC P cv m dstar n * n ≤
        piC P cv m dstar (min N (nMin P dstar)) * min N (nMin P dstar)) ∧
    (∀ n ∈ Set.Icc 0 N, piC P cv m dstar n * n =
        piC P cv m dstar (min N (nMin P dstar)) * min N (nMin P dstar) →
        n = min N (nMin P dstar)) ∧
    piC P cv m dstar (min N (nMin P dstar)) * min N (nMin P dstar) =
      (P.w0 - cv) * min N (nMin P dstar) := by
  have hd := av_dstar_ge P ha hr0 ht2 hw0 halpha m hm hloose dstar hdstar
  have hdpos : 0 < dstar := by linarith
  have hns : 0 < nMin P dstar := av_nMin_pos P ha hr0 ht2 dstar hdpos
  have hsm := av_nMin_sm P ha hr0 ht2
  set ns := nMin P dstar with hnsdef
  have hwc' : 0 < P.w0 - cv := by linarith
  -- low branch
  have F1 : ∀ n, n < ns → piC P cv m dstar n * n = (P.w0 - cv) * n := by
    intro n hn
    unfold piC
    rw [if_pos hn]
  -- high branch
  have Fh : ∀ n, ns ≤ n → piC P cv m dstar n * n =
      priceFn P m (dBar P n) * dBar P n * P.t2 - cv * n := by
    intro n hn
    have hn0 : 0 < n := lt_of_lt_of_le hns hn
    unfold piC
    rw [if_neg (not_lt.2 hn)]
    unfold uBar
    rw [(av_dBar P ha hr0 ht2 n hn0.le).2]
    field_simp
  have F2 : piC P cv m dstar ns * ns = (P.w0 - cv) * ns := by
    rw [Fh ns le_rfl]
    have hdb : dBar P ns = dstar := by
      obtain ⟨h0, h1⟩ := av_dBar P ha hr0 ht2 ns hns.le
      exact hsm.injOn (show dBar P ns ∈ Set.Ici (0:ℝ) from h0) (show dstar ∈ Set.Ici (0:ℝ) from hdpos.le)
        (by rw [h1])
    rw [hdb]
    have heq := hdstar.1.1.2.2
    have : priceFn P m dstar * dstar * P.t2 = revenue P m dstar := by unfold revenue; ring
    rw [this, heq]
    unfold hvCost wage
    rw [halpha]
    ring
  have F3 : ∀ n, ns < n → piC P cv m dstar n * n < piC P cv m dstar ns * ns := by
    intro n hn
    rw [Fh n hn.le, Fh ns le_rfl]
    exact av_Phi_anti P ha hr0 ht2 hV hw0 halpha cv hcv m hm hloose dstar hdstar
      (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hn.le) hn
  -- case analysis
  rcases le_or_gt ns N with hnsN | hNns
  · -- n0 = ns
    rw [min_eq_right hnsN]
    refine ⟨?_, ?_, F2⟩
    · intro n hn
      rcases lt_trichotomy n ns with h | h | h
      · rw [F1 n h, F2]; nlinarith
      · rw [h]
      · exact (F3 n h).le
    · intro n hn heq
      rcases lt_trichotomy n ns with h | h | h
      · rw [F1 n h, F2] at heq; nlinarith
      · exact h
      · exact absurd heq (F3 n h).ne
  · -- n0 = N < ns
    rw [min_eq_left hNns.le]
    have FN : piC P cv m dstar N * N = (P.w0 - cv) * N := F1 N hNns
    refine ⟨?_, ?_, FN⟩
    · intro n hn
      rw [F1 n (lt_of_le_of_lt hn.2 hNns), FN]
      nlinarith [hn.2]
    · intro n hn heq
      rw [F1 n (lt_of_le_of_lt hn.2 hNns), FN] at heq
      have := mul_left_cancel₀ hwc'.ne' heq
      exact this

theorem solution (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (halpha : P.alpha = 0)
    (cv cf : ℝ) (hcv : 0 < cv) (hcf : 0 < cf) (hA1 : cv + cf < P.w0)
    (m : ℝ) (hm : 0 < m) (hloose : AVRideHail.PureHV.LooseMarket P m)
    (dstar : ℝ) (hdstar : AVRideHail.PureHV.IsMaxStableEq P m dstar) (N : ℝ) (hN : 0 ≤ N) :
    IsMaxOn (fun n => piC P cv m dstar n * n) (Set.Icc 0 N) (min N (AVRideHail.PureHV.nMin P dstar)) ∧
      ∀ n ∈ Set.Icc 0 N,
        piC P cv m dstar n * n = piC P cv m dstar (min N (AVRideHail.PureHV.nMin P dstar)) * min N (AVRideHail.PureHV.nMin P dstar) →
          n = min N (AVRideHail.PureHV.nMin P dstar) := by
  obtain ⟨h1, h2, _⟩ := av_max P ha hr0.le ht2 hV (by linarith) halpha cv hcv (by linarith) m hm
    hloose dstar hdstar N hN
  refine ⟨?_, h2⟩
  rw [isMaxOn_iff]
  intro n hn
  exact h1 n hn
