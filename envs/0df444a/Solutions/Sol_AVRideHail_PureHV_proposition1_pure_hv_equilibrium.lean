-- Prove2me | solution 1 for AVRideHail.PureHV.proposition1_pure_hv_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T07:04:46.118181+00:00
-- url     : https://prove2.me/submissions/2a20e84e-4672-4155-9fce-042a7942e9a2

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

set_option autoImplicit false

namespace AVRideHail.PureHV.Pf8fecbd32
open AVRideHail.PureHV

lemma aTilde_nonneg (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) : 0 ≤ aTilde P := by
  unfold aTilde
  exact add_nonneg (mul_nonneg (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg ha.le _))
    (mul_nonneg (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg ha.le _))

lemma aTilde_pos (P : MarketParams) (ha : 0 < P.a) (hr : 0 < P.r) : 0 < aTilde P := by
  unfold aTilde
  exact add_pos_of_pos_of_nonneg (mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos ha _))
    (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg ha.le _))

lemma nMin_pos (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) {d : ℝ}
    (hd : 0 < d) : 0 < nMin P d := by
  unfold nMin
  exact add_pos_of_nonneg_of_pos (mul_nonneg (aTilde_nonneg P ha hr0) (Real.rpow_nonneg hd.le _))
    (mul_pos ht2 hd)

lemma nMin_lt (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x < y) : nMin P x < nMin P y := by
  unfold nMin
  have h1 : aTilde P * x ^ (1 / (P.r + 1)) ≤ aTilde P * y ^ (1 / (P.r + 1)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy.le (div_nonneg zero_le_one (by linarith)))
      (aTilde_nonneg P ha hr0)
  have h2 : P.t2 * x < P.t2 * y := mul_lt_mul_of_pos_left hxy ht2
  linarith

lemma f_cont (P : MarketParams) (hr0 : 0 ≤ P.r) (m : ℝ) :
    Continuous fun d => revenue P m d - hvCost P d := by
  have hc : Continuous fun d : ℝ => d ^ (1 / (P.r + 1)) :=
    Real.continuous_rpow_const (div_nonneg zero_le_one (by linarith))
  unfold revenue hvCost priceFn wage nMin
  fun_prop

lemma key (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (ht2 : 0 < P.t2) (hw0 : 0 < P.w0)
    (halpha : 0 ≤ P.alpha) (m : ℝ) (hm : 0 < m) (hl : LooseMarket P m) :
    ∃ d0, m / 2 < d0 ∧ d0 < m ∧ revenue P m d0 = hvCost P d0 ∧
      ∀ x, d0 < x → x ≤ m → revenue P m x < hvCost P x := by
  set f : ℝ → ℝ := fun d => revenue P m d - hvCost P d with hf
  have hfc : Continuous f := f_cont P hr0 m
  have hfm : f m < 0 := by
    have h1 : revenue P m m = 0 := by
      unfold revenue priceFn; rw [div_self hm.ne']; ring
    have hn := nMin_pos P ha hr0 ht2 hm
    have h2 : 0 < hvCost P m := by
      unfold hvCost wage
      exact mul_pos (add_pos_of_pos_of_nonneg hw0 (mul_nonneg halpha hn.le)) hn
    simp only [hf]; linarith
  have hfh : 0 < f (m / 2) := by
    simp only [hf]; unfold LooseMarket at hl; linarith
  have hle : m / 2 ≤ m := by linarith
  have hSc : IsCompact (Set.Icc (m / 2) m ∩ f ⁻¹' {0}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hfc)
  have hSne : (Set.Icc (m / 2) m ∩ f ⁻¹' {0}).Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle hfc.continuousOn ⟨hfm.le, hfh.le⟩
    exact ⟨c, hc, hc0⟩
  obtain ⟨d0, ⟨hd0I, hd0z⟩, hd0g⟩ := hSc.exists_isGreatest hSne
  have hz : f d0 = 0 := hd0z
  have hneg : ∀ x, d0 < x → x ≤ m → f x < 0 := by
    intro x hx hxm
    by_contra h
    push_neg at h
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hxm hfc.continuousOn ⟨hfm.le, h⟩
    have hcS : c ∈ Set.Icc (m / 2) m ∩ f ⁻¹' {0} :=
      ⟨⟨by linarith [hd0I.1, hc.1], hc.2⟩, hc0⟩
    have := hd0g hcS
    linarith [hc.1]
  refine ⟨d0, ?_, ?_, ?_, ?_⟩
  · rcases eq_or_lt_of_le hd0I.1 with h | h
    · rw [← h] at hz; linarith
    · exact h
  · rcases eq_or_lt_of_le hd0I.2 with h | h
    · rw [h] at hz; linarith
    · exact h
  · simp only [hf] at hz; linarith
  · intro x hx hxm
    have := hneg x hx hxm
    simp only [hf] at this; linarith

lemma isMax (P : MarketParams) (m d0 : ℝ) (hm : 0 < m) (h1 : m / 2 < d0) (h2 : d0 < m)
    (heq : revenue P m d0 = hvCost P d0)
    (hneg : ∀ x, d0 < x → x ≤ m → revenue P m x < hvCost P x) : IsMaxStableEq P m d0 := by
  constructor
  · refine ⟨⟨by linarith, h2.le, heq⟩, ?_⟩
    rintro ⟨ε, hε, _, hεm, _, h4⟩
    have := hneg (d0 + ε) (by linarith) hεm
    linarith
  · rintro x ⟨⟨_, hxm, hxe⟩, _⟩
    by_contra h
    push_neg at h
    have := hneg x h hxm
    linarith

lemma revenue_lt (P : MarketParams) (hV : 0 < P.V) (ht2 : 0 < P.t2) {d m1 m2 : ℝ} (hd : 0 < d)
    (hm1 : 0 < m1) (hmij : m1 < m2) : revenue P m1 d < revenue P m2 d := by
  have hm2 : 0 < m2 := hm1.trans hmij
  have h : d / m2 < d / m1 := by
    rw [div_lt_div_iff₀ hm2 hm1]; nlinarith
  unfold revenue priceFn
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (by linarith) hV) hd) ht2

lemma uBar_lt (P : MarketParams) (ha : 0 < P.a) (hr : 0 < P.r) (ht2 : 0 < P.t2) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) : uBar P x < uBar P y := by
  have hy : 0 < y := hx.trans hxy
  have hA : 0 < aTilde P := aTilde_pos P ha hr
  have hnx := nMin_pos P ha hr.le ht2 hx
  have hny := nMin_pos P ha hr.le ht2 hy
  have hp1 : 1 / (P.r + 1) - 1 < 0 := by
    rw [div_sub_one (by linarith)]; apply div_neg_of_neg_of_pos <;> linarith
  have hpow : y ^ (1 / (P.r + 1) - 1) < x ^ (1 / (P.r + 1) - 1) := Real.rpow_lt_rpow_of_neg hx hxy hp1
  have hxp : x ^ (1 / (P.r + 1)) = x ^ (1 / (P.r + 1) - 1) * x := by
    rw [Real.rpow_sub_one hx.ne']; field_simp
  have hyp : y ^ (1 / (P.r + 1)) = y ^ (1 / (P.r + 1) - 1) * y := by
    rw [Real.rpow_sub_one hy.ne']; field_simp
  unfold uBar
  rw [div_lt_div_iff₀ hnx hny]
  unfold nMin
  rw [hxp, hyp]
  have := mul_pos (mul_pos (mul_pos ht2 hA) (mul_pos hx hy)) (sub_pos.2 hpow)
  nlinarith [this]

lemma uBar_const (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r) (hr : P.r = 0)
    (ht2 : 0 < P.t2) {d : ℝ} (hd : 0 < d) : uBar P d = P.t2 / (aTilde P + P.t2) := by
  have hA := aTilde_nonneg P ha hr0
  have h1 : (1 : ℝ) / (P.r + 1) = 1 := by rw [hr]; norm_num
  unfold uBar nMin
  rw [h1, Real.rpow_one]
  rw [div_eq_div_iff (by nlinarith) (by linarith)]
  ring

end AVRideHail.PureHV.Pf8fecbd32

open AVRideHail.PureHV in
theorem solution (P : MarketParams) (ha : 0 < P.a) (hr0 : 0 ≤ P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (hw0 : 0 < P.w0) (halpha : 0 ≤ P.alpha)
    (I : ℕ) (m : Fin I → ℝ) (hm : StrictMono m) (hmpos : ∀ i, 0 < m i)
    (hloose : ∀ i, LooseMarket P (m i)) :
    (∀ i, ∃! d, IsMaxStableEq P (m i) d) ∧
      ∀ dstar : Fin I → ℝ, (∀ i, IsMaxStableEq P (m i) (dstar i)) →
        (∀ i, 0 < dstar i ∧ revenue P (m i) (dstar i) = hvCost P (dstar i) ∧
            priceFn P (m i) (dstar i) = wage P (nMin P (dstar i)) / uBar P (dstar i)) ∧
          StrictMono dstar ∧
          ((0 < P.r → StrictMono fun i => uBar P (dstar i)) ∧
            (P.r = 0 → ∀ i j, uBar P (dstar i) = uBar P (dstar j))) ∧
          StrictMono fun i => nMin P (dstar i) := by
  have hkey := fun i => Pf8fecbd32.key P ha hr0 ht2 hw0 halpha (m i) (hmpos i) (hloose i)
  choose d0 hlo hhi heq hneg using hkey
  have hmax : ∀ i, IsMaxStableEq P (m i) (d0 i) := fun i =>
    Pf8fecbd32.isMax P (m i) (d0 i) (hmpos i) (hlo i) (hhi i) (heq i) (hneg i)
  have hpos : ∀ i, 0 < d0 i := fun i => by linarith [hlo i, hmpos i]
  refine ⟨fun i => ⟨d0 i, hmax i, fun d hd => hd.unique (hmax i)⟩, ?_⟩
  intro dstar hds
  have hfun : dstar = d0 := funext fun i => (hds i).unique (hmax i)
  subst hfun
  have hsm : StrictMono dstar := by
    intro i j hij
    have hmij := hm hij
    have hr := Pf8fecbd32.revenue_lt P hV ht2 (hpos i) (hmpos i) hmij
    by_contra hc
    push_neg at hc
    rcases eq_or_lt_of_le hc with h | h
    · have := heq j
      rw [h] at this
      linarith [heq i]
    · have := hneg j (dstar i) h (by linarith [hhi i])
      linarith [heq i]
  refine ⟨fun i => ⟨hpos i, heq i, ?_⟩, hsm, ⟨?_, ?_⟩, ?_⟩
  · have hn := Pf8fecbd32.nMin_pos P ha hr0 ht2 (hpos i)
    have hdt : dstar i * P.t2 ≠ 0 := (mul_pos (hpos i) ht2).ne'
    unfold uBar
    rw [div_div_eq_mul_div, eq_div_iff hdt]
    have h := heq i
    unfold revenue hvCost at h
    linear_combination h
  · intro hr i j hij
    exact Pf8fecbd32.uBar_lt P ha hr ht2 (hpos i) (hsm hij)
  · intro hr i j
    rw [Pf8fecbd32.uBar_const P ha hr0 hr ht2 (hpos i), Pf8fecbd32.uBar_const P ha hr0 hr ht2 (hpos j)]
  · intro i j hij
    exact Pf8fecbd32.nMin_lt P ha hr0 ht2 (hpos i).le (hsm hij)
