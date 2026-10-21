-- Prove2me | solution 1 for ArtShortage.CashSubsidy.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:13:54.017861+00:00
-- url     : https://prove2.me/submissions/80505b13-5fbe-496b-8e49-9ed1599a3944

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model


namespace ASP

noncomputable section

/-- normalized non-subsidized buyers -/
def nN (f x : ℝ) : ℝ := max 0 (1 - max f x)
/-- normalized subsidized buyers -/
def sN (k f x : ℝ) : ℝ := max 0 (f - max 0 (x - k))
def DN (k f x : ℝ) : ℝ := nN f x + sN k f x

def BRN (k f x : ℝ) : Prop :=
  0 ≤ x ∧ (∀ x', 0 ≤ x' → x' * DN k f x' ≤ x * DN k f x) ∧
    (∀ x', 0 ≤ x' → x' * DN k f x' = x * DN k f x → DN k f x' ≤ DN k f x)

lemma nN_nonneg (f x : ℝ) : 0 ≤ nN f x := le_max_left _ _
lemma sN_nonneg (k f x : ℝ) : 0 ≤ sN k f x := le_max_left _ _

lemma nN_le (f x : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) : nN f x ≤ 1 - f := by
  unfold nN; apply max_le (by linarith); linarith [le_max_left f x]

lemma sN_le (k f x : ℝ) (hf : 0 ≤ f) : sN k f x ≤ f := by
  unfold sN; apply max_le hf; linarith [le_max_left 0 (x - k)]

lemma DN_le_one (k f x : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) : DN k f x ≤ 1 := by
  unfold DN; linarith [nN_le f x hf hf1, sN_le k f x hf]

lemma nN_lip (f x x' : ℝ) (h : x ≤ x') : nN f x - (x' - x) ≤ nN f x' := by
  unfold nN
  have : max f x' ≤ max f x + (x' - x) := by
    apply max_le
    · linarith [le_max_left f x]
    · linarith [le_max_right f x]
  have h0 := le_max_right 0 (1 - max f x')
  rcases le_total 0 (1 - max f x) with h1 | h1
  · rw [max_eq_right h1]; linarith
  · rw [max_eq_left h1]; linarith [le_max_left 0 (1 - max f x')]

lemma sN_lip (k f x x' : ℝ) (h : x ≤ x') : sN k f x - (x' - x) ≤ sN k f x' := by
  unfold sN
  have : max 0 (x' - k) ≤ max 0 (x - k) + (x' - x) := by
    apply max_le
    · linarith [le_max_left 0 (x - k)]
    · linarith [le_max_right 0 (x - k)]
  rcases le_total 0 (f - max 0 (x - k)) with h1 | h1
  · rw [max_eq_right h1]; linarith [le_max_right 0 (f - max 0 (x' - k))]
  · rw [max_eq_left h1]; linarith [le_max_left 0 (f - max 0 (x' - k))]

lemma DN_lip2 (k f x x' : ℝ) (h : x ≤ x') : DN k f x - 2 * (x' - x) ≤ DN k f x' := by
  unfold DN; linarith [nN_lip f x x' h, sN_lip k f x x' h]

lemma nN_of_le (f x : ℝ) (h : f ≤ x) (h1 : x ≤ 1) : nN f x = 1 - x := by
  unfold nN; rw [max_eq_right h, max_eq_right (by linarith)]

lemma nN_of_lt (f x : ℝ) (h : x ≤ f) (h1 : f ≤ 1) : nN f x = 1 - f := by
  unfold nN; rw [max_eq_left h, max_eq_right (by linarith)]

lemma nN_of_one_le (f x : ℝ) (h : 1 ≤ x) : nN f x = 0 := by
  unfold nN; apply max_eq_left; linarith [le_max_right f x]

lemma sN_of_le (k f x : ℝ) (hf : 0 ≤ f) (h : x ≤ k) : sN k f x = f := by
  unfold sN; rw [max_eq_left (show x - k ≤ 0 by linarith), sub_zero, max_eq_right hf]

lemma sN_of_gt (k f x : ℝ) (h : k ≤ x) : sN k f x = max 0 (f - (x - k)) := by
  unfold sN; rw [max_eq_right (show 0 ≤ x - k by linarith)]

lemma DN_half (k f : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) : 1 / 2 ≤ DN k f (1 / 2) := by
  unfold DN nN sN
  rcases le_total f (1/2) with h | h
  · rw [max_eq_right h]
    have h2 : (1:ℝ) - 1/2 ≤ max 0 (1 - 1/2) := le_max_right _ _
    linarith [le_max_left 0 (f - max 0 (1/2 - k))]
  · rw [max_eq_left h]
    have : max 0 (1/2 - k) ≤ 1/2 := max_le (by norm_num) (by linarith)
    have h2 : 1 - f ≤ max 0 (1 - f) := le_max_right _ _
    have h3 : f - max 0 (1/2 - k) ≤ max 0 (f - max 0 (1/2 - k)) := le_max_right _ _
    linarith

/-- F2: revenue at least 1/4 -/
lemma BR_rev_ge (k f x : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (h : BRN k f x) :
    1 / 4 ≤ x * DN k f x := by
  have := h.2.1 (1/2) (by norm_num)
  have h2 := DN_half k f hk hf hf1
  nlinarith

/-- F3: D ≤ 2x -/
lemma BR_D_le_2x (k f x : ℝ) (h : BRN k f x) : DN k f x ≤ 2 * x := by
  by_contra hc
  push Not at hc
  set D := DN k f x
  have hx0 := h.1
  set x' := (D + 2 * x) / 4
  have hx' : x ≤ x' := by simp only [x']; linarith
  have hlip := DN_lip2 k f x x' hx'
  have hbr := h.2.1 x' (by linarith)
  have hpos : 0 ≤ x' := by linarith
  have : x' * (D - 2 * (x' - x)) ≤ x' * DN k f x' := mul_le_mul_of_nonneg_left hlip hpos
  have : x' * (D - 2 * (x' - x)) - x * D = (D - 2 * x) ^ 2 / 8 := by simp only [x']; ring
  nlinarith [sq_pos_of_pos (show 0 < D - 2 * x by linarith)]

/-- LD: density-one local deviation -/
lemma BR_LD (k f x y : ℝ) (h : BRN k f x) (hxy : x < y)
    (hd : ∀ x', x ≤ x' → x' ≤ y → DN k f x - (x' - x) ≤ DN k f x') : DN k f x ≤ x := by
  by_contra hc
  push Not at hc
  set D := DN k f x
  have hx0 := h.1
  set x' := min y ((D + x) / 2)
  have h1 : x < x' := lt_min hxy (by linarith)
  have h2 : x' ≤ (D + x) / 2 := min_le_right _ _
  have h3 : x' ≤ y := min_le_left _ _
  have hbr := h.2.1 x' (by linarith)
  have hl := hd x' h1.le h3
  have : x' * (D - (x' - x)) ≤ x' * DN k f x' := mul_le_mul_of_nonneg_left hl (by linarith)
  have : x' * (D - (x' - x)) - x * D = (x' - x) * (D - x') := by ring
  have : 0 < (x' - x) * (D - x') := mul_pos (by linarith) (by linarith)
  linarith

/-- F5: transfer ≤ revenue -/
lemma BR_T_le_R (k f x : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (h : BRN k f x) :
    k * sN k f x ≤ x * DN k f x := by
  have hbr := h.2.1 k hk
  have h1 : f ≤ DN k f k := by
    unfold DN; rw [sN_of_le k f k hf le_rfl]; linarith [nN_nonneg f k]
  have h2 := sN_le k f x hf
  nlinarith

/-- in the region x < f only subsidized density -/
lemma BR_D_le_x_of_lt_f (k f x : ℝ) (hf1 : f ≤ 1) (h : BRN k f x) (hxf : x < f) :
    DN k f x ≤ x := by
  apply BR_LD k f x f h hxf
  intro x' h1 h2
  unfold DN
  rw [nN_of_lt f x (by linarith) hf1, nN_of_lt f x' h2 hf1]
  linarith [sN_lip k f x x' h1]

/-- in the region f ≤ x < k: subsidized all buy, density one -/
lemma BR_D_le_x_of_lt_k (k f x : ℝ) (hf : 0 ≤ f) (h : BRN k f x) (hxk : x < k) :
    DN k f x ≤ x := by
  apply BR_LD k f x k h hxk
  intro x' h1 h2
  unfold DN
  rw [sN_of_le k f x hf hxk.le, sN_of_le k f x' hf h2]
  linarith [nN_lip f x x' h1]

/-- F6: transfer ≤ x^2 -/
lemma BR_T_le_x2 (k f x : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (h : BRN k f x) :
    k * sN k f x ≤ x ^ 2 := by
  have hx0 := h.1
  rcases lt_or_ge x f with hxf | hxf
  · have hD := BR_D_le_x_of_lt_f k f x hf1 h hxf
    rcases lt_or_ge x k with hxk | hxk
    · exfalso
      have : DN k f x = 1 := by
        unfold DN; rw [nN_of_lt f x hxf.le hf1, sN_of_le k f x hf hxk.le]; ring
      linarith
    · have hs : sN k f x = max 0 (f - (x - k)) := sN_of_gt k f x hxk
      have hn : nN f x = 1 - f := nN_of_lt f x hxf.le hf1
      have hpos : 0 ≤ f - (x - k) := by linarith
      rw [max_eq_right hpos] at hs
      have hDv : DN k f x = 1 - x + k := by unfold DN; rw [hn, hs]; ring
      rw [hs]
      have : k ≤ 2 * x - 1 := by linarith
      nlinarith [sq_nonneg (x - 1)]
  · rcases lt_or_ge x k with hxk | hxk
    · have hD := BR_D_le_x_of_lt_k k f x hf h hxk
      have := BR_T_le_R k f x hk hf h
      nlinarith
    · rw [sN_of_gt k f x hxk]
      rcases le_total 0 (f - (x - k)) with h1 | h1
      · rw [max_eq_right h1]; nlinarith
      · rw [max_eq_left h1]; nlinarith

/-- F4: for 0 ≤ x ≤ 1, x D ≤ x(1-x) + k f -/
lemma xD_le (k f x : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * DN k f x ≤ x * (1 - x) + k * f := by
  unfold DN
  rcases le_total f x with hxf | hxf
  · rw [nN_of_le f x hxf hx1]
    rcases le_total x k with hxk | hxk
    · rw [sN_of_le k f x hf hxk]; nlinarith
    · rw [sN_of_gt k f x hxk]
      rcases le_total 0 (f - (x - k)) with h1 | h1
      · rw [max_eq_right h1]; nlinarith
      · rw [max_eq_left h1]; nlinarith
  · rw [nN_of_lt f x hxf hf1]
    rcases le_total x k with hxk | hxk
    · rw [sN_of_le k f x hf hxk]; nlinarith
    · rw [sN_of_gt k f x hxk, max_eq_right (by linarith)]; nlinarith

/-- F4': for x ≥ 1, D ≤ k f -/
lemma D_le_kf (k f x : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (hx : 1 ≤ x) :
    DN k f x ≤ k * f := by
  unfold DN
  rw [nN_of_one_le f x hx, zero_add]
  rcases le_total x k with hxk | hxk
  · rw [sN_of_le k f x hf hxk]; nlinarith
  · rw [sN_of_gt k f x hxk]
    apply max_le (by positivity)
    rcases le_total k 1 with hk1 | hk1
    · nlinarith
    · nlinarith

/-- uniqueness of the best response -/
lemma BR_unique (k f x y : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hx : BRN k f x) (hy : BRN k f y) : x = y := by
  have h1 := hx.2.1 y hy.1
  have h2 := hy.2.1 x hx.1
  have heq : y * DN k f y = x * DN k f x := le_antisymm h1 h2
  have d1 := hx.2.2 y hy.1 heq
  have d2 := hy.2.2 x hx.1 heq.symm
  have hd : DN k f y = DN k f x := le_antisymm d1 d2
  have hr := BR_rev_ge k f x hk hf hf1 hx
  have hpos : 0 < DN k f x := by
    by_contra hc; push Not at hc
    have : x * DN k f x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx.1 hc
    linarith
  rw [hd] at heq
  have := mul_right_cancel₀ hpos.ne' heq
  linarith

end

end ASP


namespace ASP

noncomputable section

def hQ (lam Q : ℝ) : ℝ := Q - Q ^ 2 / 2 + 2 * lam * Q - lam

def Ubar (Bv lam β x s : ℝ) : ℝ :=
  (1 - x ^ 2) / 2 + s ^ 2 / 2 + 2 * lam * (1 - x + s) - lam + Bv * (β - x * (1 - x + s))

def kap (β : ℝ) : ℝ := (1 + Real.sqrt (1 + 12 * β)) / 6
def xI (β : ℝ) : ℝ := 1 / 2 - Real.sqrt β
def xS (β : ℝ) : ℝ := max (kap β) (xI β)
def Wlow (Bv lam β : ℝ) : ℝ := Ubar Bv lam β (xS β) (β / xS β)
def rhoLow (β : ℝ) : ℝ := xS β * (1 - xS β) + β

lemma kap_eq (β : ℝ) (hb : 0 ≤ β) : 3 * kap β ^ 2 - kap β = β := by
  unfold kap
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 1 + 12 * β by linarith)
  nlinarith [h]

lemma kap_ge (β : ℝ) (hb : 0 ≤ β) : 1 / 3 ≤ kap β := by
  unfold kap
  have : 1 ≤ Real.sqrt (1 + 12 * β) := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + 12 * β by linarith)
    rwa [Real.sqrt_one] at this
  linarith

lemma kap_le (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) : kap β ≤ 1 / 2 := by
  unfold kap
  have : Real.sqrt (1 + 12 * β) ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

lemma xI_le (β : ℝ) : xI β ≤ 1 / 2 := by unfold xI; linarith [Real.sqrt_nonneg β]

lemma xS_ge (β : ℝ) (hb : 0 ≤ β) : 1 / 3 ≤ xS β := le_trans (kap_ge β hb) (le_max_left _ _)

lemma xS_le (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) : xS β ≤ 1 / 2 :=
  max_le (kap_le β hb hb4) (xI_le β)

/-- regime I characterisation: kap < xI -/
lemma regI_kap (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) (h : kap β < xI β) :
    2 * kap β ^ 2 < 1 / 4 := by
  have hk := kap_eq β hb
  have hk2 := kap_le β hb hb4
  unfold xI at h
  have hr := Real.sq_sqrt hb
  have hr0 := Real.sqrt_nonneg β
  have h1 : Real.sqrt β < 1 / 2 - kap β := by linarith
  have h2 : β < (1 / 2 - kap β) ^ 2 := by nlinarith
  nlinarith

lemma regII_kap (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) (h : xI β ≤ kap β) :
    1 / 4 ≤ 2 * kap β ^ 2 := by
  have hk := kap_eq β hb
  have hk2 := kap_le β hb hb4
  unfold xI at h
  have hr := Real.sq_sqrt hb
  have hr0 := Real.sqrt_nonneg β
  have h1 : 1 / 2 - kap β ≤ Real.sqrt β := by linarith
  have h2 : (1 / 2 - kap β) ^ 2 ≤ β := by nlinarith
  nlinarith

lemma Ubar_mono_s (Bv lam β x s1 s2 : ℝ) (hx1 : x ≤ 1) (hB : 0 ≤ Bv) (hs : 0 ≤ s1 + s2)
    (h12 : s1 ≤ s2) : Ubar Bv lam β x s1 + (2 * lam - Bv) * (s2 - s1) ≤ Ubar Bv lam β x s2 := by
  unfold Ubar
  nlinarith [mul_nonneg hs (show 0 ≤ s2 - s1 by linarith),
    mul_nonneg (mul_nonneg hB (show 0 ≤ 1 - x by linarith)) (show 0 ≤ s2 - s1 by linarith)]

/-- branch B: g_B is decreasing -/
lemma gB_anti (Bv lam β a y : ℝ) (hb : 0 ≤ β) (hB : 0 ≤ Bv) (hlam : 0 ≤ lam) (ha : 0 < a)
    (hay : a ≤ y) (hy1 : y ≤ 1) :
    Ubar Bv lam β y (β / y) + (2 * lam - Bv) * (y - a) ≤ Ubar Bv lam β a (β / a) := by
  have hy : 0 < y := lt_of_lt_of_le ha hay
  set p := β / a with hp
  set q := β / y with hq
  have hap : a * p = β := by rw [hp]; field_simp
  have hyq : y * q = β := by rw [hq]; field_simp
  have hq0 : 0 ≤ q := div_nonneg hb hy.le
  have hpq : q ≤ p := div_le_div_of_nonneg_left hb ha hay
  have key : Ubar Bv lam β a p - Ubar Bv lam β y q - (2 * lam - Bv) * (y - a) =
      (y ^ 2 - a ^ 2) / 2 + (p ^ 2 - q ^ 2) / 2 + 2 * lam * (p - q) +
        Bv * ((y - a) * (2 - y - a)) := by
    unfold Ubar; linear_combination (-Bv) * hap + Bv * hyq
  have t1 : 0 ≤ (y ^ 2 - a ^ 2) / 2 := by nlinarith
  have t2 : 0 ≤ (p ^ 2 - q ^ 2) / 2 := by nlinarith
  have t3 : 0 ≤ 2 * lam * (p - q) := by nlinarith
  have t4 : 0 ≤ Bv * ((y - a) * (2 - y - a)) :=
    mul_nonneg hB (mul_nonneg (by linarith) (by linarith))
  linarith

/-- branch A: g_A is increasing -/
lemma gA_mono (Bv lam β x x1 : ℝ) (hB : 0 ≤ Bv) (hlam : Bv < lam) (hx : 1 / 3 ≤ x)
    (hxx : x ≤ x1) (hx1 : x1 ≤ 1 / 2) :
    Ubar Bv lam β x (3 * x - 1) + (4 * lam - 2 * Bv - 1) * (x1 - x) ≤
      Ubar Bv lam β x1 (3 * x1 - 1) := by
  have key : Ubar Bv lam β x1 (3 * x1 - 1) - Ubar Bv lam β x (3 * x - 1) -
      (4 * lam - 2 * Bv - 1) * (x1 - x) =
      (x1 - x) * (4 * (x + x1) - 2 + 2 * Bv * (1 - x - x1)) := by
    unfold Ubar; ring
  have : 0 ≤ (x1 - x) * (4 * (x + x1) - 2 + 2 * Bv * (1 - x - x1)) := by
    apply mul_nonneg (by linarith)
    nlinarith [mul_nonneg hB (show 0 ≤ 1 - x - x1 by linarith)]
  linarith

/-- C1: the case-1 relaxed problem -/
lemma C1 (Bv lam β x s : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) (hB : 1 ≤ Bv) (hlam : Bv < lam)
    (hs : 0 ≤ s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxs : x * s ≤ β) (hD : 1 - x + s ≤ 2 * x)
    (hR : 1 / 4 ≤ x * (1 - x + s)) :
    Ubar Bv lam β x s ≤ Wlow Bv lam β ∧
      (Wlow Bv lam β ≤ Ubar Bv lam β x s → x * (1 - x + s) = rhoLow β) := by
  have hk := kap_eq β hb
  have hk3 := kap_ge β hb
  have hk2 := kap_le β hb hb4
  have hxS3 := xS_ge β hb
  have hxS2 := xS_le β hb hb4
  have hr := Real.sq_sqrt hb
  have hr0 := Real.sqrt_nonneg β
  have hx13 : 1 / 3 ≤ x := by nlinarith
  have hxpos : 0 < x := by linarith
  have hc : 0 < 2 * lam - Bv := by linarith
  rcases lt_or_ge x (kap β) with hxk | hxk
  · -- branch A
    have hs3 : s ≤ 3 * x - 1 := by linarith
    have hregII : xI β ≤ kap β := by
      by_contra hc'
      push Not at hc'
      have := regI_kap β hb hb4 hc'
      have : x * (1 - x + s) ≤ 2 * x ^ 2 := by nlinarith
      nlinarith
    have hxS : xS β = kap β := max_eq_left hregII
    have hfs : β / kap β = 3 * kap β - 1 := by
      field_simp; nlinarith
    have hW : Wlow Bv lam β = Ubar Bv lam β (kap β) (3 * kap β - 1) := by
      unfold Wlow; rw [hxS, hfs]
    have m1 := Ubar_mono_s Bv lam β x s (3 * x - 1) hx1 (by linarith) (by linarith) hs3
    have m2 := gA_mono Bv lam β x (kap β) (by linarith) hlam hx13 hxk.le hk2
    have hc2 : 0 < 4 * lam - 2 * Bv - 1 := by linarith
    refine ⟨?_, ?_⟩
    · rw [hW]; linarith [mul_nonneg hc.le (show 0 ≤ 3 * x - 1 - s by linarith),
        mul_nonneg hc2.le (show 0 ≤ kap β - x by linarith)]
    · intro heq
      exfalso
      rw [hW] at heq
      linarith [mul_nonneg hc.le (show 0 ≤ 3 * x - 1 - s by linarith),
        mul_pos hc2 (show 0 < kap β - x by linarith)]
  · -- branch B
    have hsb : s ≤ β / x := by rw [le_div_iff₀ hxpos]; linarith
    have hxI : xI β ≤ x := by
      unfold xI
      by_contra hc'
      push Not at hc'
      have h1 : Real.sqrt β < 1 / 2 - x := by linarith
      have h2 : β < (1 / 2 - x) ^ 2 := by nlinarith
      nlinarith
    have hxSx : xS β ≤ x := max_le hxk hxI
    have m1 := Ubar_mono_s Bv lam β x s (β / x) hx1 (by linarith)
      (by have := div_nonneg hb hxpos.le; linarith) hsb
    have m2 := gB_anti Bv lam β (xS β) x hb (by linarith) (by linarith) (by linarith) hxSx hx1
    refine ⟨?_, ?_⟩
    · unfold Wlow
      linarith [mul_nonneg hc.le (show 0 ≤ β / x - s by linarith),
        mul_nonneg hc.le (show 0 ≤ x - xS β by linarith)]
    · intro heq
      unfold Wlow at heq
      have e1 : (2 * lam - Bv) * (β / x - s) = 0 := by
        linarith [mul_nonneg hc.le (show 0 ≤ β / x - s by linarith),
          mul_nonneg hc.le (show 0 ≤ x - xS β by linarith)]
      have e2 : (2 * lam - Bv) * (x - xS β) = 0 := by
        linarith [mul_nonneg hc.le (show 0 ≤ β / x - s by linarith),
          mul_nonneg hc.le (show 0 ≤ x - xS β by linarith)]
      have hs' : s = β / x := by
        rcases mul_eq_zero.mp e1 with h | h
        · linarith
        · linarith
      have hx' : x = xS β := by
        rcases mul_eq_zero.mp e2 with h | h
        · linarith
        · linarith
      unfold rhoLow
      rw [hs', ← hx']
      field_simp

end

end ASP


namespace ASP

noncomputable section

def WN (Bv lam k f x : ℝ) : ℝ :=
  nN f x - nN f x ^ 2 / 2 + (f * sN k f x - sN k f x ^ 2 / 2) +
    Bv * (k * sN k f x - x * DN k f x) + 2 * lam * DN k f x - lam

lemma W_le_h (Bv lam k f x : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    WN Bv lam k f x ≤ hQ lam (DN k f x) + Bv * (k * sN k f x - x * DN k f x) := by
  have h1 := nN_le f x hf hf1
  have h2 := sN_nonneg k f x
  have key : hQ lam (DN k f x) + Bv * (k * sN k f x - x * DN k f x) - WN Bv lam k f x =
      sN k f x * (1 - nN f x - f) := by
    unfold hQ WN DN; ring
  nlinarith [mul_nonneg h2 (show 0 ≤ 1 - nN f x - f by linarith)]

lemma W_eq_h_of_lt (Bv lam k f x : ℝ) (hf1 : f ≤ 1) (hxf : x ≤ f) :
    WN Bv lam k f x = hQ lam (DN k f x) + Bv * (k * sN k f x - x * DN k f x) := by
  have h1 := nN_of_lt f x hxf hf1
  unfold hQ WN DN; rw [h1]; ring

lemma hQ_mono (lam a b : ℝ) (hlam : 0 ≤ lam) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    hQ lam a + 2 * lam * (b - a) ≤ hQ lam b := by
  unfold hQ; nlinarith [mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ 2 - a - b by linarith)]

lemma DN_anti (k f x x' : ℝ) (h : x ≤ x') : DN k f x' ≤ DN k f x := by
  unfold DN nN sN
  have a1 : max f x ≤ max f x' := max_le_max le_rfl h
  have a2 : max 0 (x - k) ≤ max 0 (x' - k) := max_le_max le_rfl (by linarith)
  have b1 : max 0 (1 - max f x') ≤ max 0 (1 - max f x) := max_le_max le_rfl (by linarith)
  have b2 : max 0 (f - max 0 (x' - k)) ≤ max 0 (f - max 0 (x - k)) :=
    max_le_max le_rfl (by linarith)
  linarith

/-! ### Regime I/II -/

lemma C2 (Bv lam β D R : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) (hB : 1 ≤ Bv) (hlam : Bv < lam)
    (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2 + 2 * β) (hR : 1 / 4 ≤ R) (hR2 : D ^ 2 ≤ R) :
    hQ lam D + Bv * (β - R) ≤ Wlow Bv lam β ∧
      (Wlow Bv lam β ≤ hQ lam D + Bv * (β - R) → R = rhoLow β) := by
  have hk := kap_eq β hb
  have hk3 := kap_ge β hb
  have hk2 := kap_le β hb hb4
  have hr := Real.sq_sqrt hb
  have hr0 := Real.sqrt_nonneg β
  set r := Real.sqrt β with hrdef
  have hBpos : 0 ≤ Bv := by linarith
  have hDm := hQ_mono lam D (1 / 2 + 2 * β) (by linarith) hD0 hD (by linarith)
  rcases lt_or_ge (kap β) (xI β) with hI | hII
  · -- regime I
    have hxIr : xI β = 1 / 2 - r := by rw [hrdef]; rfl
    have hxS : xS β = 1 / 2 - r := by rw [← hxIr]; exact max_eq_right hI.le
    have hr6 : r < 1 / 6 := by rw [hxIr] at hI; linarith
    have hxIpos : 0 < 1 / 2 - r := by linarith
    set fI := β / (1 / 2 - r) with hfI
    have hfI0 : 0 ≤ fI := div_nonneg hb hxIpos.le
    have hne : (1 / 2 - r) ≠ 0 := hxIpos.ne'
    have hxf : (1 / 2 - r) * fI = β := by rw [hfI, mul_comm]; exact div_mul_cancel₀ β hne
    have e : (1 / 2 - r) * (1 - (1 / 2 - r) + fI) = 1 / 4 := by linear_combination hxf - hr
    have hW : Wlow Bv lam β = (1 - (1 / 2 - r) ^ 2) / 2 + fI ^ 2 / 2 +
        2 * lam * (1 - (1 / 2 - r) + fI) - lam + Bv * (β - 1 / 4) := by
      unfold Wlow Ubar; rw [hxS, e]
    have hrho : rhoLow β = 1 / 4 := by
      unfold rhoLow; rw [hxS]; linear_combination (-1:ℝ) * hr
    have ident : (1 - (1 / 2 - r) ^ 2) / 2 + fI ^ 2 / 2 + 2 * lam * (1 - (1 / 2 - r) + fI) - lam
        - hQ lam (1 / 2 + 2 * β) =
        (r / 2 - 3 * r ^ 2 / 2 + 2 * r ^ 4) + fI ^ 2 / 2 + 2 * lam * (r - 2 * r ^ 2 + fI) := by
      unfold hQ; rw [← hr]; ring
    have t1 : 0 ≤ r / 2 - 3 * r ^ 2 / 2 + 2 * r ^ 4 := by
      have : 0 ≤ r * (1 - 3 * r) := mul_nonneg hr0 (by linarith)
      nlinarith [sq_nonneg (r ^ 2)]
    have t2 : 0 ≤ 2 * lam * (r - 2 * r ^ 2 + fI) :=
      mul_nonneg (by linarith) (by nlinarith)
    have t3 : 0 ≤ fI ^ 2 / 2 := by positivity
    have hBR : Bv * (β - R) ≤ Bv * (β - 1 / 4) := mul_le_mul_of_nonneg_left (by linarith) hBpos
    have hlam0 : 0 ≤ 2 * lam * (1 / 2 + 2 * β - D) := mul_nonneg (by linarith) (by linarith)
    constructor
    · rw [hW]; linarith
    · intro h; rw [hW] at h; rw [hrho]
      have : Bv * (R - 1 / 4) ≤ 0 := by linarith
      have : R - 1 / 4 ≤ 0 := by
        by_contra hcc; push Not at hcc
        have := mul_pos (show (0:ℝ) < Bv by linarith) hcc; linarith
      linarith
  · -- regime II
    have hxS : xS β = kap β := max_eq_left hII
    have hkpos : 0 < kap β := by linarith
    have hfs : β / kap β = 3 * kap β - 1 := by
      field_simp; linarith
    have hW : Wlow Bv lam β = Ubar Bv lam β (kap β) (3 * kap β - 1) := by
      unfold Wlow; rw [hxS, hfs]
    set κ := kap β
    have hD2 : D ≤ 2 * κ := by
      nlinarith [mul_nonneg (show 0 ≤ 6 * κ - 1 by linarith) (show 0 ≤ 1 - 2 * κ by linarith)]
    have m : hQ lam D - Bv * D ^ 2 ≤ hQ lam (2 * κ) - Bv * (2 * κ) ^ 2 := by
      have ident : hQ lam (2 * κ) - Bv * (2 * κ) ^ 2 - (hQ lam D - Bv * D ^ 2) =
          (2 * κ - D) * (2 * lam - 2 * Bv + (1 - (2 * κ + D) / 2) + Bv * (2 - 2 * κ - D)) := by
        unfold hQ; ring
      have : 0 ≤ (2 * κ - D) * (2 * lam - 2 * Bv + (1 - (2 * κ + D) / 2) + Bv * (2 - 2 * κ - D)) := by
        apply mul_nonneg (by linarith)
        have := mul_nonneg hBpos (show 0 ≤ 2 - 2 * κ - D by linarith)
        linarith
      linarith
    have gapid : Ubar Bv lam β κ (3 * κ - 1) - (hQ lam (2 * κ) - Bv * (2 * κ) ^ 2 + Bv * β) =
        6 * κ ^ 2 - 5 * κ + 1 + 2 * Bv * κ ^ 2 := by
      unfold hQ Ubar; ring
    have gap : 0 < 6 * κ ^ 2 - 5 * κ + 1 + 2 * Bv * κ ^ 2 := by
      have h1 : 1 * κ ^ 2 ≤ Bv * κ ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg κ)
      have h2 : 0 ≤ (κ - 5 / 16) ^ 2 := sq_nonneg _
      have h3 : 6 * κ ^ 2 - 5 * κ + 1 + 2 * Bv * κ ^ 2 =
          8 * (κ - 5 / 16) ^ 2 + 7 / 32 + 2 * (Bv * κ ^ 2 - 1 * κ ^ 2) := by ring
      linarith only [h1, h2, h3]
    have hBR : Bv * (β - R) ≤ Bv * (β - D ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hBpos
    constructor
    · rw [hW]; linarith only [m, gapid, gap, hBR]
    · intro h; exfalso; rw [hW] at h; linarith only [m, gapid, gap, hBR, h]

theorem UB_low (Bv lam β k f x : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) (hB : 1 ≤ Bv)
    (hlam : Bv < lam) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (hkf : k * f ≤ β)
    (h : BRN k f x) :
    WN Bv lam k f x ≤ Wlow Bv lam β ∧
      (Wlow Bv lam β ≤ WN Bv lam k f x → x * DN k f x = rhoLow β ∧ k * f = β) := by
  have hx0 := h.1
  have hR := BR_rev_ge k f x hk hf hf1 h
  have hD2 := BR_D_le_2x k f x h
  have hTR := BR_T_le_R k f x hk hf h
  have hs0 := sN_nonneg k f x
  have hsf := sN_le k f x hf
  have hD0 : 0 ≤ DN k f x := by unfold DN; linarith [nN_nonneg f x]
  have hTb : k * sN k f x ≤ β := le_trans (mul_le_mul_of_nonneg_left hsf hk) hkf
  have hWh := W_le_h Bv lam k f x hf hf1
  have hBpos : 0 ≤ Bv := by linarith
  rcases lt_or_ge 1 x with hx1 | hx1
  · -- case 3
    have hDk := D_le_kf k f x hk hf hf1 hx1.le
    have hm := hQ_mono lam (DN k f x) β (by linarith) hD0 (by linarith) (by linarith)
    have hc1 := (C1 Bv lam β (1 / 2) (2 * β) hb hb4 hB hlam (by linarith) (by norm_num)
      (by norm_num) (by linarith) (by linarith) (by nlinarith)).1
    have hlt : hQ lam β < Ubar Bv lam β (1 / 2) (2 * β) := by
      unfold hQ Ubar; nlinarith
    have hW1 : WN Bv lam k f x ≤ hQ lam (DN k f x) := by
      nlinarith [mul_nonneg hBpos (show 0 ≤ x * DN k f x - k * sN k f x by linarith)]
    have hlam0 : 0 ≤ 2 * lam * (β - DN k f x) := by nlinarith
    refine ⟨by linarith, fun h' => by exfalso; linarith⟩
  · rcases le_or_gt f x with hfx | hfx
    · -- case 1
      have hn : nN f x = 1 - x := nN_of_le f x hfx hx1
      have hDv : DN k f x = 1 - x + sN k f x := by unfold DN; rw [hn]
      have hsk : sN k f x ≤ k := by
        rcases le_total x k with hxk | hxk
        · linarith
        · rw [sN_of_gt k f x hxk]; exact max_le hk (by linarith)
      have hxs : x * sN k f x ≤ k * f := by
        have := xD_le k f x hk hf hf1 hx0 hx1
        rw [hDv] at this; nlinarith
      have key : WN Bv lam k f x - (Ubar Bv lam β x (sN k f x) - Bv * (β - k * f)) =
          (f - sN k f x) * (sN k f x - Bv * k) := by
        unfold WN Ubar; rw [hn, hDv]; ring
      have hneg : (f - sN k f x) * (sN k f x - Bv * k) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
      have hc := C1 Bv lam β x (sN k f x) hb hb4 hB hlam hs0 hx0 hx1 (by linarith)
        (by rw [hDv] at hD2; linarith) (by rw [hDv] at hR; linarith)
      refine ⟨by nlinarith [mul_nonneg hBpos (show 0 ≤ β - k * f by linarith)], fun h' => ?_⟩
      have hU : Wlow Bv lam β ≤ Ubar Bv lam β x (sN k f x) := by
        nlinarith [mul_nonneg hBpos (show 0 ≤ β - k * f by linarith)]
      have hR' := hc.2 hU
      refine ⟨by rw [hDv]; exact hR', ?_⟩
      have : Bv * (β - k * f) ≤ 0 := by linarith [hc.1]
      have : β - k * f ≤ 0 := by
        by_contra hcc; push Not at hcc; nlinarith
      linarith
    · -- case 2
      have hWe := W_eq_h_of_lt Bv lam k f x hf1 hfx.le
      have hDx := BR_D_le_x_of_lt_f k f x hf1 h hfx
      have hx2 : 1 / 2 ≤ x := by nlinarith
      have hxpos : 0 < x := by linarith
      have hDb : DN k f x ≤ 1 / 2 + 2 * β := by
        have h1 := xD_le k f x hk hf hf1 hx0 hx1
        have h2 : x * DN k f x ≤ x * (1 - x + 2 * β) := by nlinarith
        have := le_of_mul_le_mul_left h2 hxpos
        linarith
      have hc := C2 Bv lam β (DN k f x) (x * DN k f x) hb hb4 hB hlam hD0 hDb hR (by nlinarith)
      refine ⟨by nlinarith [mul_nonneg hBpos (show 0 ≤ β - k * sN k f x by linarith)],
        fun h' => ?_⟩
      have hU : Wlow Bv lam β ≤ hQ lam (DN k f x) + Bv * (β - x * DN k f x) := by
        nlinarith [mul_nonneg hBpos (show 0 ≤ β - k * sN k f x by linarith)]
      refine ⟨hc.2 hU, ?_⟩
      have : Bv * (β - k * sN k f x) ≤ 0 := by nlinarith [hc.1]
      have : β - k * sN k f x ≤ 0 := by
        by_contra hcc; push Not at hcc; nlinarith
      have : k * sN k f x ≤ k * f := mul_le_mul_of_nonneg_left hsf hk
      linarith

end

end ASP


namespace ASP

noncomputable section

lemma E_bound (x D T β r : ℝ) (hx : 0 ≤ x) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hD2 : D ≤ 2 * x)
    (hTb : T ≤ β) (hTx : T ≤ x ^ 2) (hr : r ^ 2 = β) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) :
    -2 * (1 - D) + T - x * D ≤ β - r := by
  rcases le_or_gt 2 x with h2 | h2
  · nlinarith [mul_nonneg hD0 (show 0 ≤ x - 2 by linarith)]
  rcases le_or_gt r x with h3 | h3
  · nlinarith [mul_nonneg (show 0 ≤ 1 - D by linarith) (show 0 ≤ 2 - x by linarith)]
  rcases le_or_gt (1 / 2) x with h4 | h4
  · nlinarith [mul_nonneg (show 0 ≤ 1 - D by linarith) (show 0 ≤ 2 - x by linarith),
      mul_nonneg (show 0 ≤ r - x by linarith) (show 0 ≤ x + r - 1 by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ 2 * x - D by linarith) (show 0 ≤ 2 - x by linarith),
      mul_pos (show 0 < 1 / 2 - x by linarith) (show 0 < 7 / 2 - x by linarith),
      sq_nonneg (r - 1 / 2)]

lemma E_eq (x T β r : ℝ) (h : T - x = β - r) (hTb : T ≤ β) (hTx : T ≤ x ^ 2)
    (hx2 : 1 ≤ 2 * x) (hr : r ^ 2 = β) (hr1 : 1 / 2 ≤ r) : x = r ∧ T = β := by
  rcases le_or_gt r x with h3 | h3
  · constructor <;> linarith
  · exfalso
    nlinarith [mul_pos (show 0 < r - x by linarith) (show 0 < x + r - 1 by linarith)]

theorem UB_mid (Bv lam β r k f x : ℝ) (hr : r ^ 2 = β) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1)
    (hB : 1 ≤ Bv) (hlam : Bv < lam) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hkf : k * f ≤ β) (h : BRN k f x) :
    WN Bv lam k f x ≤ hQ lam 1 + Bv * (β - r) ∧
      (hQ lam 1 + Bv * (β - r) ≤ WN Bv lam k f x → x * DN k f x = r ∧ k * f = β) := by
  have hx0 := h.1
  have hD2 := BR_D_le_2x k f x h
  have hs0 := sN_nonneg k f x
  have hsf := sN_le k f x hf
  have hD0 : 0 ≤ DN k f x := by unfold DN; linarith [nN_nonneg f x]
  have hD1 := DN_le_one k f x hf hf1
  have hTb : k * sN k f x ≤ β := le_trans (mul_le_mul_of_nonneg_left hsf hk) hkf
  have hTx := BR_T_le_x2 k f x hk hf hf1 h
  have hWh := W_le_h Bv lam k f x hf hf1
  have hm := hQ_mono lam (DN k f x) 1 (by linarith) hD0 hD1 le_rfl
  have hE := E_bound x (DN k f x) (k * sN k f x) β r hx0 hD0 hD1 hD2 hTb hTx hr hr1 hr2
  set D := DN k f x
  set T := k * sN k f x
  have hBpos : 0 ≤ Bv := by linarith
  have key : WN Bv lam k f x ≤ hQ lam 1 + Bv * (β - r) - 2 * (lam - Bv) * (1 - D) -
      Bv * ((β - r) - (-2 * (1 - D) + T - x * D)) := by nlinarith
  have p1 : 0 ≤ 2 * (lam - Bv) * (1 - D) := mul_nonneg (by linarith) (by linarith)
  have p2 : 0 ≤ Bv * ((β - r) - (-2 * (1 - D) + T - x * D)) := mul_nonneg hBpos (by linarith)
  refine ⟨by linarith, fun heq => ?_⟩
  have e1 : 2 * (lam - Bv) * (1 - D) = 0 := by linarith
  have e2 : Bv * ((β - r) - (-2 * (1 - D) + T - x * D)) = 0 := by linarith
  have hD : D = 1 := by
    rcases mul_eq_zero.mp e1 with h' | h'
    · exfalso; linarith
    · linarith
  have hE' : (β - r) - (-2 * (1 - D) + T - x * D) = 0 := by
    rcases mul_eq_zero.mp e2 with h' | h'
    · exfalso; linarith
    · exact h'
  rw [hD] at hE'
  have hxr := E_eq x T β r (by linarith) hTb hTx (by rw [hD] at hD2; linarith) hr hr1
  refine ⟨by rw [hD, hxr.1]; ring, ?_⟩
  have : T ≤ k * f := mul_le_mul_of_nonneg_left hsf hk
  linarith [hxr.2]

theorem UB_high (Bv lam k f x : ℝ) (hB : 1 ≤ Bv) (hlam : Bv < lam) (hk : 0 ≤ k) (hf : 0 ≤ f)
    (hf1 : f ≤ 1) (h : BRN k f x) :
    WN Bv lam k f x ≤ hQ lam 1 ∧
      (hQ lam 1 ≤ WN Bv lam k f x → DN k f x = 1 ∧ k * sN k f x = x * DN k f x) := by
  have hTR := BR_T_le_R k f x hk hf h
  have hD0 : 0 ≤ DN k f x := by unfold DN; linarith [nN_nonneg f x, sN_nonneg k f x]
  have hD1 := DN_le_one k f x hf hf1
  have hWh := W_le_h Bv lam k f x hf hf1
  have hm := hQ_mono lam (DN k f x) 1 (by linarith) hD0 hD1 le_rfl
  have hBpos : 0 ≤ Bv := by linarith
  have p1 : 0 ≤ Bv * (x * DN k f x - k * sN k f x) := mul_nonneg hBpos (by linarith)
  have p2 : 0 ≤ 2 * lam * (1 - DN k f x) := mul_nonneg (by linarith) (by linarith)
  refine ⟨by nlinarith, fun heq => ?_⟩
  have e1 : 2 * lam * (1 - DN k f x) = 0 := by nlinarith
  have e2 : Bv * (x * DN k f x - k * sN k f x) = 0 := by nlinarith
  constructor
  · rcases mul_eq_zero.mp e1 with h' | h'
    · exfalso; linarith
    · linarith
  · rcases mul_eq_zero.mp e2 with h' | h'
    · exfalso; linarith
    · linarith

/-- structure of welfare-optimal policies in the high regime -/
lemma high_struct (k f x : ℝ) (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (h : BRN k f x)
    (hD : DN k f x = 1) (hT : k * sN k f x = x * DN k f x) : f = 1 ∧ 1 ≤ k ∧ x = k := by
  have hx0 := h.1
  have hR := BR_rev_ge k f x hk hf hf1 h
  have hn := nN_le f x hf hf1
  have hs := sN_le k f x hf
  have hss : sN k f x = f := by unfold DN at hD; linarith [nN_nonneg f x]
  have hnn : nN f x = 1 - f := by unfold DN at hD; linarith
  rw [hss, hD, mul_one] at hT
  -- hT : k * f = x
  have hbr := h.2.1 k hk
  have hDk : DN k f k = nN f k + f := by unfold DN; rw [sN_of_le k f k hf le_rfl]
  rw [hDk, hD, mul_one] at hbr
  have hkn : k * nN f k ≤ 0 := by nlinarith
  have hkpos : 0 < k := by
    rcases eq_or_lt_of_le hk with h0 | h0
    · exfalso; rw [← h0] at hT; rw [hD] at hR; linarith
    · exact h0
  have hnk : nN f k = 0 := by
    have := nN_nonneg f k
    by_contra hc
    have : 0 < nN f k := lt_of_le_of_ne this (Ne.symm hc)
    nlinarith
  rcases eq_or_lt_of_le hf1 with hf1' | hf1'
  · -- f = 1
    have hxk : x = k := by rw [← hT, hf1', mul_one]
    refine ⟨hf1', ?_, hxk⟩
    by_contra hc; push Not at hc
    set x' := (1 + k) / 2 with hx'
    have hbr2 := h.2.1 x' (by rw [hx']; linarith)
    have hn1 : nN f x' = 0 := by
      unfold nN; rw [hf1']; apply max_eq_left; linarith [le_max_left (1:ℝ) x']
    have hs1 : sN k f x' = (1 + k) / 2 := by
      rw [sN_of_gt k f x' (by rw [hx']; linarith), hf1', max_eq_right (by rw [hx']; linarith)]
      rw [hx']; ring
    have hDx' : DN k f x' = (1 + k) / 2 := by unfold DN; rw [hn1, hs1]; ring
    rw [hDx', hD, hxk] at hbr2
    nlinarith [sq_pos_of_pos (show 0 < 1 - k by linarith)]
  · -- f < 1
    exfalso
    have hk1 : 1 ≤ k := by
      unfold nN at hnk
      by_contra hc; push Not at hc
      have h1 : max f k < 1 := max_lt hf1' hc
      have : 0 < 1 - max f k := by linarith
      rw [max_eq_right this.le] at hnk; linarith
    have hxf : x ≤ f := by
      unfold nN at hnn
      rcases le_total 0 (1 - max f x) with h0 | h0
      · rw [max_eq_right h0] at hnn
        have : max f x = f := by linarith
        rw [← this]; exact le_max_right f x
      · rw [max_eq_left h0] at hnn; linarith
    have hxeq : x = f := by nlinarith
    have hfpos : 0 < f := by rw [hD] at hR; linarith
    set x' := (1 + f) / 2 with hx'
    have hbr2 := h.2.1 x' (by rw [hx']; linarith)
    have hn1 : nN f x' = 1 - x' := nN_of_le f x' (by rw [hx']; linarith) (by rw [hx']; linarith)
    have hs1 : sN k f x' = f := sN_of_le k f x' hf (by rw [hx']; linarith)
    have hDx' : DN k f x' = 1 - x' + f := by unfold DN; rw [hn1, hs1]
    rw [hDx', hD, hxeq] at hbr2
    rw [hx'] at hbr2
    nlinarith [sq_pos_of_pos (show 0 < 1 - f by linarith)]

end

end ASP


namespace ASP

noncomputable section

lemma BR_of (k f x : ℝ) (hx : 0 ≤ x)
    (hlt : ∀ x', 0 ≤ x' → x' < x → x' * DN k f x' < x * DN k f x)
    (hge : ∀ x', x ≤ x' → x' * DN k f x' ≤ x * DN k f x) : BRN k f x := by
  refine ⟨hx, fun x' hx' => ?_, fun x' hx' heq => ?_⟩
  · rcases lt_or_ge x' x with h | h
    · exact (hlt x' hx' h).le
    · exact hge x' h
  · rcases lt_or_ge x' x with h | h
    · exfalso; have := hlt x' hx' h; linarith
    · exact DN_anti k f x x' h

lemma nN_one (y : ℝ) : nN 1 y = 0 := by
  unfold nN; apply max_eq_left; linarith [le_max_left (1:ℝ) y]

theorem EX_low (Bv lam β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) :
    BRN (xS β) (β / xS β) (xS β) ∧ WN Bv lam (xS β) (β / xS β) (xS β) = Wlow Bv lam β ∧
      xS β * DN (xS β) (β / xS β) (xS β) = rhoLow β ∧ xS β * (β / xS β) = β := by
  have hk := kap_eq β hb
  have hk3 := kap_ge β hb
  have hk2 := kap_le β hb hb4
  have hx3 := xS_ge β hb
  have hx2 := xS_le β hb hb4
  have hr := Real.sq_sqrt hb
  have hr0 := Real.sqrt_nonneg β
  have hxk : kap β ≤ xS β := le_max_left _ _
  have hxi : xI β ≤ xS β := le_max_right _ _
  set k := xS β with hkdef
  have hkpos : 0 < k := by linarith
  set f := β / k with hfdef
  have hkf : k * f = β := by rw [hfdef]; field_simp
  have hf0 : 0 ≤ f := div_nonneg hb hkpos.le
  -- f ≤ k
  have hfk : f ≤ k := by
    have h1 : β ≤ k ^ 2 := by nlinarith
    nlinarith
  -- vertex condition 3k ≥ 1 + f
  have hvert : 1 + f ≤ 3 * k := by
    have : β ≤ 3 * k ^ 2 - k := by nlinarith
    nlinarith
  -- revenue at least 1/4
  have hR4 : 1 / 4 ≤ k * (1 - k) + β := by
    unfold xI at hxi
    have h1 : 1 / 2 - k ≤ Real.sqrt β := by linarith
    have h2 : (1 / 2 - k) ^ 2 ≤ β := by nlinarith
    nlinarith
  have hnk : nN f k = 1 - k := nN_of_le f k hfk (by linarith)
  have hsk : sN k f k = f := sN_of_le k f k hf0 le_rfl
  have hDk : DN k f k = 1 - k + f := by unfold DN; rw [hnk, hsk]
  have hRk : k * DN k f k = k * (1 - k) + β := by rw [hDk, ← hkf]; ring
  refine ⟨?_, ?_, ?_, hkf⟩
  · apply BR_of k f k hkpos.le
    · intro x' hx0 hx'
      rw [hRk]
      have hs' : sN k f x' = f := sN_of_le k f x' hf0 hx'.le
      rcases le_total x' f with h1 | h1
      · have hn' : nN f x' = 1 - f := nN_of_lt f x' h1 (by linarith)
        have : DN k f x' = 1 := by unfold DN; rw [hn', hs']; ring
        rw [this, ← hkf]
        nlinarith [mul_nonneg hkpos.le (show 0 ≤ x' - f + (k - x') by linarith),
          mul_pos (show 0 < k - x' by linarith) (show 0 < 1 - k by linarith)]
      · have hn' : nN f x' = 1 - x' := nN_of_le f x' h1 (by linarith)
        have : DN k f x' = 1 - x' + f := by unfold DN; rw [hn', hs']
        rw [this, ← hkf]
        nlinarith [mul_pos (show 0 < k - x' by linarith) (show 0 < 1 + f - k - x' by linarith)]
    · intro x' hx'
      rw [hRk]
      rcases le_total x' (k + f) with h1 | h1
      · have hn' : nN f x' = 1 - x' := nN_of_le f x' (by linarith) (by linarith)
        have hs' : sN k f x' = f + k - x' := by
          rw [sN_of_gt k f x' hx', max_eq_right (by linarith)]; ring
        have : DN k f x' = 1 + k + f - 2 * x' := by unfold DN; rw [hn', hs']; ring
        rw [this, ← hkf]
        nlinarith [mul_nonneg (show 0 ≤ x' - k by linarith) (show 0 ≤ k + 2 * x' - 1 - f by linarith)]
      · have hs' : sN k f x' = 0 := by
          rw [sN_of_gt k f x' hx', max_eq_left (by linarith)]
        have : DN k f x' = nN f x' := by unfold DN; rw [hs', add_zero]
        rw [this]
        unfold nN
        rcases le_total 0 (1 - max f x') with h2 | h2
        · rw [max_eq_right h2]
          have : max f x' = x' := max_eq_right (by linarith)
          rw [this]; nlinarith [sq_nonneg (x' - 1 / 2)]
        · rw [max_eq_left h2]; nlinarith
  · unfold WN Wlow Ubar
    rw [← hkdef, ← hfdef, hnk, hsk, hDk]
    have : β = k * f := hkf.symm
    rw [this]; ring
  · rw [hRk]; unfold rhoLow; rfl

theorem EX_mid (Bv lam β r : ℝ) (hr : r ^ 2 = β) (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) :
    BRN r r r ∧ WN Bv lam r r r = hQ lam 1 + Bv * (β - r) ∧ r * DN r r r = r ∧ r * r = β := by
  have hn : nN r r = 1 - r := nN_of_le r r le_rfl hr2
  have hs : sN r r r = r := sN_of_le r r r (by linarith) le_rfl
  have hD : DN r r r = 1 := by unfold DN; rw [hn, hs]; ring
  refine ⟨?_, ?_, by rw [hD]; ring, by rw [← hr]; ring⟩
  · apply BR_of r r r (by linarith)
    · intro x' hx0 hx'
      have hn' : nN r x' = 1 - r := nN_of_lt r x' hx'.le hr2
      have hs' : sN r r x' = r := sN_of_le r r x' (by linarith) hx'.le
      have : DN r r x' = 1 := by unfold DN; rw [hn', hs']; ring
      rw [this, hD]; linarith
    · intro x' hx'
      rw [hD]
      rcases le_total x' 1 with h1 | h1
      · have hn' : nN r x' = 1 - x' := nN_of_le r x' hx' h1
        have hs' : sN r r x' = 2 * r - x' := by
          rw [sN_of_gt r r x' hx', max_eq_right (by linarith)]; ring
        have : DN r r x' = 1 + 2 * r - 2 * x' := by unfold DN; rw [hn', hs']; ring
        rw [this]
        nlinarith [mul_nonneg (show 0 ≤ 2 * x' - 1 by linarith) (show 0 ≤ x' - r by linarith)]
      · have hn' : nN r x' = 0 := nN_of_one_le r x' h1
        rw [show DN r r x' = sN r r x' by unfold DN; rw [hn', zero_add]]
        rw [sN_of_gt r r x' hx']
        rcases le_total 0 (r - (x' - r)) with h2 | h2
        · rw [max_eq_right h2]; nlinarith [sq_nonneg (x' - r)]
        · rw [max_eq_left h2]; nlinarith
  · unfold WN hQ; rw [hn, hs, hD, ← hr]; ring

theorem EX_high (Bv lam : ℝ) :
    BRN 1 1 1 ∧ WN Bv lam 1 1 1 = hQ lam 1 ∧ (1:ℝ) * DN 1 1 1 = 1 ∧ (1:ℝ) * 1 = 1 := by
  have hn : ∀ y, nN 1 y = 0 := nN_one
  have hs : sN 1 1 1 = 1 := sN_of_le 1 1 1 (by norm_num) le_rfl
  have hD : DN 1 1 1 = 1 := by unfold DN; rw [hn, hs]; ring
  refine ⟨?_, ?_, by rw [hD]; ring, by ring⟩
  · apply BR_of 1 1 1 (by norm_num)
    · intro x' hx0 hx'
      have hs' : sN 1 1 x' = 1 := sN_of_le 1 1 x' (by norm_num) hx'.le
      have : DN 1 1 x' = 1 := by unfold DN; rw [hn, hs']; ring
      rw [this, hD]; linarith
    · intro x' hx'
      rw [hD, show DN 1 1 x' = sN 1 1 x' by unfold DN; rw [hn, zero_add], sN_of_gt 1 1 x' hx']
      rcases le_total 0 (1 - (x' - 1)) with h2 | h2
      · rw [max_eq_right h2]; nlinarith [sq_nonneg (x' - 1)]
      · rw [max_eq_left h2]; nlinarith
  · unfold WN hQ; rw [hn, hs, hD]; ring

end

end ASP


namespace ASP

open ArtShortage.CashSubsidy

noncomputable section

def rho (β : ℝ) : ℝ := if β ≤ 1 / 4 then rhoLow β else min (Real.sqrt β) 1

def Wst (Bv lam β : ℝ) : ℝ :=
  if β ≤ 1 / 4 then Wlow Bv lam β else if β ≤ 1 then hQ lam 1 + Bv * (β - Real.sqrt β)
  else hQ lam 1

theorem UB_all (Bv lam β k f x : ℝ) (hb : 0 ≤ β) (hB : 1 ≤ Bv) (hlam : Bv < lam)
    (hk : 0 ≤ k) (hf : 0 ≤ f) (hf1 : f ≤ 1) (hkf : k * f ≤ β) (h : BRN k f x) :
    WN Bv lam k f x ≤ Wst Bv lam β ∧
      (Wst Bv lam β ≤ WN Bv lam k f x →
        (β ≤ 1 → x * DN k f x = rho β ∧ k * f = β) ∧
        (1 < β → f = 1 ∧ 1 ≤ k ∧ x = k ∧ DN k f x = 1)) := by
  unfold Wst rho
  by_cases h4 : β ≤ 1 / 4
  · simp only [h4, if_true]
    have := UB_low Bv lam β k f x hb h4 hB hlam hk hf hf1 hkf h
    exact ⟨this.1, fun he => ⟨fun _ => this.2 he, fun h1 => by exfalso; first | exact h1 | linarith⟩⟩
  · simp only [h4, if_false]
    push Not at h4
    by_cases h1 : β ≤ 1
    · simp only [h1, if_true]
      have hr := Real.sq_sqrt hb
      have hr1 : 1 / 2 ≤ Real.sqrt β := by
        rw [show (1:ℝ)/2 = Real.sqrt (1/4) by
          rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt h4.le
      have hr2 : Real.sqrt β ≤ 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
      have := UB_mid Bv lam β (Real.sqrt β) k f x hr hr1 hr2 hB hlam hk hf hf1 hkf h
      refine ⟨this.1, fun he => ⟨fun _ => ?_, fun h' => by exfalso; first | exact h' | linarith⟩⟩
      rw [min_eq_left hr2]; exact this.2 he
    · simp only [h1, if_false]
      push Not at h1
      have := UB_high Bv lam k f x hB hlam hk hf hf1 h
      refine ⟨this.1, fun he => ⟨fun h' => by exfalso; first | exact h' | linarith, fun _ => ?_⟩⟩
      obtain ⟨hD, hT⟩ := this.2 he
      have := high_struct k f x hk hf hf1 h hD hT
      exact ⟨this.1, this.2.1, this.2.2, hD⟩

theorem EX_all (Bv lam β : ℝ) (hb : 0 ≤ β) :
    ∃ k f x, 0 ≤ k ∧ 0 ≤ f ∧ f ≤ 1 ∧ k * f = min β 1 ∧ BRN k f x ∧
      WN Bv lam k f x = Wst Bv lam β ∧ x * DN k f x = rho β := by
  unfold Wst rho
  by_cases h4 : β ≤ 1 / 4
  · simp only [h4, if_true]
    obtain ⟨h1, h2, h3, h5⟩ := EX_low Bv lam β hb h4
    have hx3 := xS_ge β hb
    have hx2 := xS_le β hb h4
    have hf0 : 0 ≤ β / xS β := div_nonneg hb (by linarith)
    have hfk : β / xS β ≤ 1 := by
      rw [div_le_one (by linarith)]; nlinarith [kap_eq β hb, kap_ge β hb, le_max_left (kap β) (xI β)]
    exact ⟨xS β, β / xS β, xS β, by linarith, hf0, hfk,
      by rw [h5, min_eq_left (by linarith)], h1, h2, h3⟩
  · simp only [h4, if_false]
    push Not at h4
    by_cases h1 : β ≤ 1
    · simp only [h1, if_true]
      have hr := Real.sq_sqrt hb
      have hr1 : 1 / 2 ≤ Real.sqrt β := by
        rw [show (1:ℝ)/2 = Real.sqrt (1/4) by
          rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt h4.le
      have hr2 : Real.sqrt β ≤ 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
      obtain ⟨e1, e2, e3, e4⟩ := EX_mid Bv lam β (Real.sqrt β) hr hr1 hr2
      exact ⟨_, _, _, by linarith, by linarith, hr2, by rw [e4, min_eq_left h1], e1, e2,
        by rw [e3, min_eq_left hr2]⟩
    · simp only [h1, if_false]
      push Not at h1
      obtain ⟨e1, e2, e3, e4⟩ := EX_high Bv lam
      have hs1 : 1 ≤ Real.sqrt β := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le
      exact ⟨1, 1, 1, by norm_num, by norm_num, le_rfl, by rw [min_eq_right h1.le]; ring, e1, e2,
        by rw [e3, min_eq_right hs1]⟩

/-! ### Link with the platform model -/

lemma B_bounds (g lam q : ℝ) (hS : Standing g lam) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    1 ≤ B g q ∧ B g q < lam := by
  obtain ⟨hg, _, hl⟩ := hS
  obtain ⟨h0, h1⟩ := hq
  unfold B
  constructor
  · nlinarith
  · nlinarith

lemma demand_eq (g q c f p : ℝ) :
    demand g q c f p = DN (c / B g q) f (p / B g q) := by
  unfold demand nonsubBuyers subBuyers DN nN sN
  rw [sub_div]

lemma BR_iff (g q c f p : ℝ) (hB : 0 < B g q) :
    IsTraderBR g q c f p ↔ BRN (c / B g q) f (p / B g q) := by
  unfold IsTraderBR BRN
  simp only [demand_eq]
  set Bq := B g q
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨div_nonneg h0 hB.le, fun x' hx' => ?_, fun x' hx' heq => ?_⟩
    · have := h1 (x' * Bq) (mul_nonneg hx' hB.le)
      rw [mul_div_cancel_right₀ x' hB.ne'] at this
      have e : p * DN (c / Bq) f (p / Bq) = Bq * (p / Bq * DN (c / Bq) f (p / Bq)) := by
        field_simp
      nlinarith
    · have := h2 (x' * Bq) (mul_nonneg hx' hB.le)
      rw [mul_div_cancel_right₀ x' hB.ne'] at this
      apply this
      have e : p * DN (c / Bq) f (p / Bq) = Bq * (p / Bq * DN (c / Bq) f (p / Bq)) := by
        field_simp
      rw [e, ← heq]; ring
  · rintro ⟨h0, h1, h2⟩
    have hp : 0 ≤ p := by
      have := mul_nonneg h0 hB.le; rwa [div_mul_cancel₀ p hB.ne'] at this
    refine ⟨hp, fun p' hp' => ?_, fun p' hp' heq => ?_⟩
    · have := h1 (p' / Bq) (div_nonneg hp' hB.le)
      have e1 : p' * DN (c / Bq) f (p' / Bq) = Bq * (p' / Bq * DN (c / Bq) f (p' / Bq)) := by
        field_simp
      have e2 : p * DN (c / Bq) f (p / Bq) = Bq * (p / Bq * DN (c / Bq) f (p / Bq)) := by
        field_simp
      rw [e1, e2]; exact mul_le_mul_of_nonneg_left this hB.le
    · apply h2 (p' / Bq) (div_nonneg hp' hB.le)
      have e1 : p' * DN (c / Bq) f (p' / Bq) = Bq * (p' / Bq * DN (c / Bq) f (p' / Bq)) := by
        field_simp
      have e2 : p * DN (c / Bq) f (p / Bq) = Bq * (p / Bq * DN (c / Bq) f (p / Bq)) := by
        field_simp
      rw [e1, e2] at heq
      exact mul_left_cancel₀ hB.ne' heq

lemma int_one_sub (a b : ℝ) : ∫ q in a..b, (1 - q) = (b - a) - (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]

lemma CW2_eq (g lam q c f p : ℝ) (hB : 0 < B g q) :
    CW2 g lam q c f p = WN (B g q) lam (c / B g q) f (p / B g q) := by
  unfold CW2 WN DN
  simp only [int_one_sub]
  have hn : nonsubBuyers g q f p = nN f (p / B g q) := rfl
  have hs : subBuyers g q c f p = sN (c / B g q) f (p / B g q) := by
    unfold subBuyers sN; rw [sub_div]
  rw [hn, hs]
  field_simp
  ring

lemma rev_eq (g q c f p : ℝ) (hB : 0 < B g q) :
    p * demand g q c f p = B g q * (p / B g q * DN (c / B g q) f (p / B g q)) := by
  rw [demand_eq]; field_simp

end

end ASP


namespace ASP

open ArtShortage.CashSubsidy

noncomputable section

lemma feas_iff (b c f Bq : ℝ) (hB : 0 < Bq) :
    Feasible b c f ↔ 0 ≤ c / Bq ∧ 0 ≤ f ∧ f ≤ 1 ∧ c / Bq * f ≤ b / Bq := by
  unfold Feasible
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨div_nonneg h1 hB.le, h2, h3, ?_⟩
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h4 hB.le
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h2, h3, ?_⟩
    · have := mul_nonneg h1 hB.le; rwa [div_mul_cancel₀ c hB.ne'] at this
    · rw [div_mul_eq_mul_div] at h4; exact (div_le_div_iff_of_pos_right hB).mp h4

section
variable (g lam b q : ℝ)

lemma govOpt_iff (hS : Standing g lam) (hq : q ∈ Set.Icc (0:ℝ) 1) (hb : 0 ≤ b) (c f : ℝ) :
    IsGovOpt g lam b q c f ↔ Feasible b c f ∧ ∃ p, IsTraderBR g q c f p ∧
      CW2 g lam q c f p = Wst (B g q) lam (b / B g q) := by
  obtain ⟨hB1, hBl⟩ := B_bounds g lam q hS hq
  have hB : 0 < B g q := by linarith
  set Bq := B g q
  have hβ : 0 ≤ b / Bq := div_nonneg hb hB.le
  obtain ⟨k0, f0, x0, hk0, hf0, hf01, hkf0, hbr0, hW0, -⟩ := EX_all Bq lam (b / Bq) hβ
  have hF0 : Feasible b (k0 * Bq) f0 := by
    rw [feas_iff b _ f0 Bq hB, mul_div_cancel_right₀ k0 hB.ne']
    exact ⟨hk0, hf0, hf01, by rw [hkf0]; exact min_le_left _ _⟩
  have hBR0 : IsTraderBR g q (k0 * Bq) f0 (x0 * Bq) := by
    rw [BR_iff g q _ f0 _ hB, mul_div_cancel_right₀ k0 hB.ne', mul_div_cancel_right₀ x0 hB.ne']
    exact hbr0
  have hCW0 : CW2 g lam q (k0 * Bq) f0 (x0 * Bq) = Wst Bq lam (b / Bq) := by
    rw [CW2_eq g lam q _ f0 _ hB, mul_div_cancel_right₀ k0 hB.ne',
      mul_div_cancel_right₀ x0 hB.ne']
    exact hW0
  have UB : ∀ c' f' p', Feasible b c' f' → IsTraderBR g q c' f' p' →
      CW2 g lam q c' f' p' ≤ Wst Bq lam (b / Bq) := by
    intro c' f' p' hF hbr
    rw [feas_iff b c' f' Bq hB] at hF
    rw [BR_iff g q c' f' p' hB] at hbr
    rw [CW2_eq g lam q c' f' p' hB]
    exact (UB_all Bq lam (b / Bq) _ f' _ hβ hB1 hBl hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hbr).1
  constructor
  · rintro ⟨hF, p, hbr, hall⟩
    refine ⟨hF, p, hbr, le_antisymm (UB c f p hF hbr) ?_⟩
    rw [← hCW0]; exact hall _ _ _ hF0 hBR0
  · rintro ⟨hF, p, hbr, heq⟩
    refine ⟨hF, p, hbr, fun c' f' p' hF' hbr' => ?_⟩
    rw [heq]; exact UB c' f' p' hF' hbr'

theorem gov_choice_exists (hS : Standing g lam) (hq : q ∈ Set.Icc (0:ℝ) 1) (hb : 0 ≤ b) :
    ∃ c f p, IsGovChoice g lam b q c f ∧ IsTraderBR g q c f p := by
  obtain ⟨hB1, hBl⟩ := B_bounds g lam q hS hq
  have hB : 0 < B g q := by linarith
  set Bq := B g q
  have hβ : 0 ≤ b / Bq := div_nonneg hb hB.le
  obtain ⟨k0, f0, x0, hk0, hf0, hf01, hkf0, hbr0, hW0, -⟩ := EX_all Bq lam (b / Bq) hβ
  have hF0 : Feasible b (k0 * Bq) f0 := by
    rw [feas_iff b _ f0 Bq hB, mul_div_cancel_right₀ k0 hB.ne']
    exact ⟨hk0, hf0, hf01, by rw [hkf0]; exact min_le_left _ _⟩
  have hBR0 : IsTraderBR g q (k0 * Bq) f0 (x0 * Bq) := by
    rw [BR_iff g q _ f0 _ hB, mul_div_cancel_right₀ k0 hB.ne', mul_div_cancel_right₀ x0 hB.ne']
    exact hbr0
  have hCW0 : CW2 g lam q (k0 * Bq) f0 (x0 * Bq) = Wst Bq lam (b / Bq) := by
    rw [CW2_eq g lam q _ f0 _ hB, mul_div_cancel_right₀ k0 hB.ne',
      mul_div_cancel_right₀ x0 hB.ne']
    exact hW0
  have hOpt0 : IsGovOpt g lam b q (k0 * Bq) f0 :=
    (govOpt_iff g lam b q hS hq hb _ _).mpr ⟨hF0, _, hBR0, hCW0⟩
  refine ⟨k0 * Bq, f0, x0 * Bq, ⟨hOpt0, fun c' f' hO => ?_⟩, hBR0⟩
  obtain ⟨hF, p, hbr, heq⟩ := (govOpt_iff g lam b q hS hq hb c' f').mp hO
  rw [feas_iff b c' f' Bq hB] at hF
  rw [BR_iff g q c' f' p hB] at hbr
  rw [CW2_eq g lam q c' f' p hB] at heq
  have hU := (UB_all Bq lam (b / Bq) _ f' _ hβ hB1 hBl hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hbr).2
    heq.symm.le
  have e1 : k0 * Bq * f0 = Bq * min (b / Bq) 1 := by rw [← hkf0]; ring
  have e2 : c' * f' = Bq * (c' / Bq * f') := by field_simp
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hB.le
  rcases le_or_gt (b / Bq) 1 with h1 | h1
  · rw [(hU.1 h1).2]; exact min_le_left _ _
  · obtain ⟨hf1, hk1, -, -⟩ := hU.2 h1
    rw [hf1, mul_one, min_eq_right h1.le]; exact hk1

theorem rev_of_choice (hS : Standing g lam) (hq : q ∈ Set.Icc (0:ℝ) 1) (hb : 0 ≤ b)
    (c f p : ℝ) (hc : IsGovChoice g lam b q c f) (hp : IsTraderBR g q c f p) :
    p * demand g q c f p = B g q * rho (b / B g q) := by
  obtain ⟨hB1, hBl⟩ := B_bounds g lam q hS hq
  have hB : 0 < B g q := by linarith
  obtain ⟨hO, hleast⟩ := hc
  obtain ⟨hF, p0, hbr0, heq⟩ := (govOpt_iff g lam b q hS hq hb c f).mp hO
  set Bq := B g q
  have hβ : 0 ≤ b / Bq := div_nonneg hb hB.le
  rw [feas_iff b c f Bq hB] at hF
  rw [BR_iff g q c f p0 hB] at hbr0
  rw [BR_iff g q c f p hB] at hp
  have hpp := BR_unique _ f _ _ hF.1 hF.2.1 hF.2.2.1 hp hbr0
  rw [CW2_eq g lam q c f p0 hB, ← hpp] at heq
  have hU := (UB_all Bq lam (b / Bq) _ f _ hβ hB1 hBl hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hp).2
    heq.symm.le
  rw [rev_eq g q c f p hB]
  congr 1
  rcases le_or_gt (b / Bq) 1 with h1 | h1
  · exact (hU.1 h1).1
  · obtain ⟨hf1, hk1, hxk, hD⟩ := hU.2 h1
    -- compare with the exhibited policy (Bq, 1)
    obtain ⟨k0, f0, x0, hk0, hf0, hf01, hkf0, hbr0', hW0, -⟩ := EX_all Bq lam (b / Bq) hβ
    have hF0 : Feasible b (k0 * Bq) f0 := by
      rw [feas_iff b _ f0 Bq hB, mul_div_cancel_right₀ k0 hB.ne']
      exact ⟨hk0, hf0, hf01, by rw [hkf0]; exact min_le_left _ _⟩
    have hBR0 : IsTraderBR g q (k0 * Bq) f0 (x0 * Bq) := by
      rw [BR_iff g q _ f0 _ hB, mul_div_cancel_right₀ k0 hB.ne', mul_div_cancel_right₀ x0 hB.ne']
      exact hbr0'
    have hCW0 : CW2 g lam q (k0 * Bq) f0 (x0 * Bq) = Wst Bq lam (b / Bq) := by
      rw [CW2_eq g lam q _ f0 _ hB, mul_div_cancel_right₀ k0 hB.ne',
        mul_div_cancel_right₀ x0 hB.ne']
      exact hW0
    have hOpt0 : IsGovOpt g lam b q (k0 * Bq) f0 :=
      (govOpt_iff g lam b q hS hq hb _ _).mpr ⟨hF0, _, hBR0, hCW0⟩
    have hl := hleast _ _ hOpt0
    have e1 : k0 * Bq * f0 = Bq * min (b / Bq) 1 := by rw [← hkf0]; ring
    have e2 : c * f = Bq * (c / Bq * f) := by field_simp
    rw [e1, e2, hf1, mul_one, min_eq_right h1.le] at hl
    have hk : c / Bq ≤ 1 := by
      have := le_of_mul_le_mul_left hl hB; linarith
    have hk' : c / Bq = 1 := le_antisymm hk hk1
    have hrho : rho (b / Bq) = 1 := by
      unfold rho
      have : ¬ (b / Bq ≤ 1 / 4) := by linarith
      simp only [this, if_false]
      apply min_eq_right
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le
    rw [hrho, hD, hxk, hk']; ring

end

def TT (g b q : ℝ) : ℝ := q * (1 - q) + B g q * rho (b / B g q)

theorem EqQ1_char (g lam b : ℝ) (hS : Standing g lam) (hb : 0 ≤ b) :
    EqQ1 g lam b = {q | q ∈ Set.Icc (0:ℝ) 1 ∧ ∀ q' ∈ Set.Icc (0:ℝ) 1, TT g b q' ≤ TT g b q} := by
  ext q
  simp only [EqQ1, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hq, σ, hσ, hmax⟩
    refine ⟨hq, fun q' hq' => ?_⟩
    have h1 := hmax q' hq'
    unfold totalRev at h1
    rw [rev_of_choice g lam b q' hS hq' hb _ _ _ (hσ q' hq').1 (hσ q' hq').2,
      rev_of_choice g lam b q hS hq hb _ _ _ (hσ q hq).1 (hσ q hq).2] at h1
    unfold TT; linarith
  · rintro ⟨hq, hmax⟩
    refine ⟨hq, fun q' => if h : q' ∈ Set.Icc (0:ℝ) 1 then
      ((gov_choice_exists g lam b q' hS h hb).choose,
        (gov_choice_exists g lam b q' hS h hb).choose_spec.choose,
        (gov_choice_exists g lam b q' hS h hb).choose_spec.choose_spec.choose) else (0, 0, 0),
      fun q' hq' => ?_, fun q' hq' => ?_⟩
    · simp only [hq', dif_pos]
      exact (gov_choice_exists g lam b q' hS hq' hb).choose_spec.choose_spec.choose_spec
    · simp only [hq', hq, dif_pos]
      unfold totalRev
      have s1 := (gov_choice_exists g lam b q' hS hq' hb).choose_spec.choose_spec.choose_spec
      have s2 := (gov_choice_exists g lam b q hS hq hb).choose_spec.choose_spec.choose_spec
      rw [rev_of_choice g lam b q' hS hq' hb _ _ _ s1.1 s1.2,
        rev_of_choice g lam b q hS hq hb _ _ _ s2.1 s2.2]
      have := hmax q' hq'
      unfold TT at this; linarith

end

end ASP


namespace ASP

noncomputable section

lemma kap_mono {a b : ℝ} (hab : a ≤ b) : kap a ≤ kap b := by
  unfold kap
  have := Real.sqrt_le_sqrt (show 1 + 12 * a ≤ 1 + 12 * b by linarith)
  linarith

lemma kap_strictMono {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : kap a < kap b := by
  unfold kap
  have := Real.sqrt_lt_sqrt (show 0 ≤ 1 + 12 * a by linarith) (show 1 + 12 * a < 1 + 12 * b by linarith)
  linarith

lemma rhoLow_eq_max (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) :
    rhoLow β = max (1 / 4) (2 * kap β ^ 2) := by
  have hk := kap_eq β hb
  have hr := Real.sq_sqrt hb
  unfold rhoLow xS
  rcases lt_or_ge (kap β) (xI β) with h | h
  · rw [max_eq_right h.le, max_eq_left (regI_kap β hb hb4 h).le]
    unfold xI; nlinarith
  · rw [max_eq_left h, max_eq_right (regII_kap β hb hb4 h)]
    nlinarith

lemma kap_quarter : kap (1 / 4) = 1 / 2 := by
  unfold kap
  rw [show (1:ℝ) + 12 * (1 / 4) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

lemma sqrt_quarter : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1:ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma rhoLow_quarter : rhoLow (1 / 4) = 1 / 2 := by
  rw [rhoLow_eq_max _ (by norm_num) le_rfl, kap_quarter]; norm_num

lemma rho_of_le (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) : rho β = max (1 / 4) (2 * kap β ^ 2) := by
  unfold rho; rw [if_pos hb4, rhoLow_eq_max β hb hb4]

lemma rho_of_ge (β : ℝ) (hb4 : 1 / 4 ≤ β) : rho β = min (Real.sqrt β) 1 := by
  unfold rho
  rcases eq_or_lt_of_le hb4 with h | h
  · rw [← h, if_pos le_rfl, rhoLow_quarter, sqrt_quarter]; norm_num
  · rw [if_neg (by linarith)]

lemma sqrt_ge_half (β : ℝ) (hb4 : 1 / 4 ≤ β) : 1 / 2 ≤ Real.sqrt β := by
  rw [← sqrt_quarter]; exact Real.sqrt_le_sqrt hb4

lemma rho_ge (β : ℝ) (hb : 0 ≤ β) : 1 / 4 ≤ rho β := by
  rcases le_total β (1 / 4) with h | h
  · rw [rho_of_le β hb h]; exact le_max_left _ _
  · rw [rho_of_ge β h]; have := sqrt_ge_half β h
    exact le_min (by linarith) (by norm_num)

lemma rho_le_half (β : ℝ) (hb : 0 ≤ β) (hb4 : β ≤ 1 / 4) : rho β ≤ 1 / 2 := by
  rw [rho_of_le β hb hb4]
  have := kap_le β hb hb4; have := kap_ge β hb
  apply max_le (by norm_num); nlinarith

lemma rho_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : rho a ≤ rho b := by
  rcases le_total b (1 / 4) with hb | hb
  · rw [rho_of_le a ha (by linarith), rho_of_le b (by linarith) hb]
    apply max_le_max le_rfl
    have := kap_mono hab; have := kap_ge a ha
    nlinarith
  · rw [rho_of_ge b hb]
    rcases le_total a (1 / 4) with ha4 | ha4
    · have := rho_le_half a ha ha4
      have := sqrt_ge_half b hb
      exact le_min (by linarith) (by linarith)
    · rw [rho_of_ge a ha4]
      exact min_le_min (Real.sqrt_le_sqrt hab) le_rfl

lemma rhoLow_cont : Continuous rhoLow := by
  unfold rhoLow xS kap xI
  fun_prop

lemma rho_cont : Continuous rho := by
  unfold rho
  apply Continuous.if_le rhoLow_cont (by fun_prop) continuous_id continuous_const
  intro x hx
  simp only [id] at hx
  rw [hx, rhoLow_quarter, sqrt_quarter]; norm_num

lemma rho_small (β : ℝ) (hb : 0 ≤ β) (hb64 : β ≤ 1 / 64) : rho β = 1 / 4 := by
  rw [rho_of_le β hb (by linarith)]
  apply max_eq_left
  have h1 : Real.sqrt (1 + 12 * β) ≤ 1.09 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have h2 : kap β ≤ 2.09 / 6 := by unfold kap; linarith
  have h3 := kap_ge β hb
  nlinarith

lemma rho_eq_quarter_lt (β : ℝ) (hb : 0 ≤ β) (h : rho β = 1 / 4) : β < 1 / 16 := by
  by_contra hc; push Not at hc
  rcases le_total β (1 / 4) with h4 | h4
  · rw [rho_of_le β hb h4] at h
    have h1 : (1.32:ℝ) ≤ Real.sqrt (1 + 12 * β) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
    have h2 : 2.32 / 6 ≤ kap β := by unfold kap; linarith
    have : 2 * kap β ^ 2 ≤ 1 / 4 := by rw [← h]; exact le_max_right _ _
    nlinarith
  · have := rho_ge β hb
    rw [rho_of_ge β h4] at h
    have := sqrt_ge_half β h4
    have : (1:ℝ) / 2 ≤ min (Real.sqrt β) 1 := le_min (by linarith) (by norm_num)
    linarith

/-- strict increase of rho where it exceeds 1/4, up to 1 -/
lemma rho_strict {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (hra : 1 / 4 < rho a) :
    rho a < rho b := by
  rcases le_or_gt b (1 / 4) with hb | hb
  · rw [rho_of_le a ha (by linarith)] at hra ⊢
    rw [rho_of_le b (by linarith) hb]
    have h1 : max (1 / 4) (2 * kap a ^ 2) = 2 * kap a ^ 2 := by
      rcases le_total (1/4 : ℝ) (2 * kap a ^ 2) with h | h
      · exact max_eq_right h
      · rw [max_eq_left h] at hra; linarith
    rw [h1]
    have := kap_strictMono ha hab; have := kap_ge a ha
    have : 2 * kap a ^ 2 < 2 * kap b ^ 2 := by nlinarith
    exact lt_of_lt_of_le this (le_max_right _ _)
  · rw [rho_of_ge b hb.le]
    have hsb1 : Real.sqrt b ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
    rw [min_eq_left hsb1]
    rcases le_total a (1 / 4) with ha4 | ha4
    · have h1 := rho_le_half a ha ha4
      have : 1 / 2 < Real.sqrt b := by
        rw [← sqrt_quarter]; exact Real.sqrt_lt_sqrt (by norm_num) hb
      linarith
    · rw [rho_of_ge a ha4]
      have hsa : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha hab
      exact lt_of_le_of_lt (min_le_left _ _) hsa

/-! ### the regime boundary β1 -/

def κ1 : ℝ := Real.sqrt 2 / 4
def β1 : ℝ := 3 * κ1 ^ 2 - κ1

lemma sqrt2_bounds : (1.414 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma κ1_sq : κ1 ^ 2 = 1 / 8 := by
  unfold κ1; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma β1_bounds : 1 / 64 < β1 ∧ β1 < 1 / 4 := by
  unfold β1; rw [κ1_sq]; unfold κ1
  obtain ⟨h1, h2⟩ := sqrt2_bounds
  constructor <;> linarith

lemma kap_β1 : kap β1 = κ1 := by
  unfold kap
  have hs : Real.sqrt (1 + 12 * β1) = 6 * κ1 - 1 := by
    have h0 : 0 ≤ 6 * κ1 - 1 := by unfold κ1; linarith [sqrt2_bounds.1]
    rw [Real.sqrt_eq_iff_mul_self_eq (by linarith [β1_bounds.1]) h0]
    unfold β1; nlinarith [κ1_sq]
  rw [hs]; ring

lemma rho_β1 : rho β1 = 1 / 4 := by
  rw [rho_of_le β1 (by linarith [β1_bounds.1]) (by linarith [β1_bounds.2]), kap_β1, κ1_sq]
  norm_num

lemma rho_gt_quarter_imp (β : ℝ) (hb : 0 ≤ β) (h : 1 / 4 < rho β) : β1 < β := by
  by_contra hc; push Not at hc
  have := rho_mono hb hc
  rw [rho_β1] at this; linarith

lemma rho_chord_β1 (β : ℝ) (h1 : β1 ≤ β) (h4 : β ≤ 1 / 4) : 1 / 4 + (β - β1) ≤ rho β := by
  have hb : 0 ≤ β := by linarith [β1_bounds.1]
  rw [rho_of_le β hb h4]
  have hk := kap_eq β hb
  have hk1 : κ1 ≤ kap β := by rw [← kap_β1]; exact kap_mono h1
  have hk2 := kap_le β hb h4
  have hκ1 : κ1 < 1 / 2 := by unfold κ1; linarith [sqrt2_bounds.2]
  have e : β1 = 3 * κ1 ^ 2 - κ1 := rfl
  have : 1 / 4 + (β - β1) ≤ 2 * kap β ^ 2 := by
    have hp := mul_nonneg (show 0 ≤ kap β - κ1 by linarith) (show 0 ≤ 1 - kap β - κ1 by linarith)
    have hq := κ1_sq
    nlinarith
  exact le_trans this (le_max_right _ _)

/-! ### slope-type monotonicity of (rho - 1/4)/β -/

lemma phi_mono_low (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb4 : b ≤ 1 / 4) :
    b * (rho a - 1 / 4) ≤ a * (rho b - 1 / 4) := by
  have hb : 0 ≤ b := by linarith
  have hra := rho_ge a ha.le
  have hrb := rho_ge b hb
  rcases eq_or_lt_of_le hra with h | h
  · rw [← h]; nlinarith
  · rw [rho_of_le a ha.le (by linarith)] at h ⊢
    rw [rho_of_le b hb hb4]
    have h1 : max (1 / 4) (2 * kap a ^ 2) = 2 * kap a ^ 2 := by
      rcases le_total (1/4 : ℝ) (2 * kap a ^ 2) with h' | h'
      · exact max_eq_right h'
      · rw [max_eq_left h'] at h; linarith
    rw [h1]
    have hka := kap_eq a ha.le
    have hkb := kap_eq b hb
    have hab' := kap_mono hab
    have hka3 := kap_ge a ha.le
    have hkb2 := kap_le b hb hb4
    set ka := kap a
    set kb := kap b
    have key : a * (2 * kb ^ 2 - 1 / 4) - b * (2 * ka ^ 2 - 1 / 4) =
        (kb - ka) * (-(8 * ka * kb - 3 * ka - 3 * kb + 1)) / 4 := by
      rw [← hka, ← hkb]; ring
    have hneg : 8 * ka * kb - 3 * ka - 3 * kb + 1 ≤ 0 := by
      have : (ka - 3 / 8) * (kb - 3 / 8) ≤ 1 / 64 := by
        rcases le_total (3/8 : ℝ) ka with h2 | h2
        · nlinarith
        · rcases le_total (3/8 : ℝ) kb with h3 | h3
          · nlinarith
          · nlinarith
      nlinarith
    have : 0 ≤ a * (2 * kb ^ 2 - 1 / 4) - b * (2 * ka ^ 2 - 1 / 4) := by
      rw [key]; apply div_nonneg _ (by norm_num)
      exact mul_nonneg (by linarith) (by linarith)
    have : 2 * kb ^ 2 ≤ max (1 / 4) (2 * kb ^ 2) := le_max_right _ _
    nlinarith

lemma phi_anti_high (a b : ℝ) (ha : 1 / 4 ≤ a) (hab : a ≤ b) :
    a * (rho b - 1 / 4) ≤ b * (rho a - 1 / 4) := by
  rw [rho_of_ge a ha, rho_of_ge b (by linarith)]
  have hsa := sqrt_ge_half a ha
  have hsb := sqrt_ge_half b (by linarith)
  have hab' : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have ea := Real.sq_sqrt (show (0:ℝ) ≤ a by linarith)
  have eb := Real.sq_sqrt (show (0:ℝ) ≤ b by linarith)
  set sa := Real.sqrt a
  set sb := Real.sqrt b
  rw [← ea, ← eb]
  rcases le_total sb 1 with h1 | h1
  · rw [min_eq_left h1, min_eq_left (by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ sb - sa by linarith)
      (show 0 ≤ sa * sb - (sa + sb) / 4 by nlinarith)]
  · rw [min_eq_right h1]
    rcases le_total sa 1 with h2 | h2
    · rw [min_eq_left h2]
      nlinarith [mul_nonneg (show 0 ≤ 3 * sa - 1 by linarith) (show 0 ≤ 1 - sa by linarith),
        mul_nonneg (show 0 ≤ sb ^ 2 - 1 by nlinarith) (show 0 ≤ sa - 1 / 4 by linarith)]
    · rw [min_eq_right h2]; nlinarith

end

end ASP


namespace ASP

open Set Filter Topology

noncomputable section

def F1 (β : ℝ) : ℝ := (1 + 6 * β + Real.sqrt (1 + 12 * β)) / 9
def G (β : ℝ) : ℝ := if β ≤ 1 / 4 then F1 β else Real.sqrt β
def G' (β : ℝ) : ℝ :=
  if β ≤ 1 / 4 then (6 + 12 / (2 * Real.sqrt (1 + 12 * β))) / 9 else 1 / (2 * Real.sqrt β)

lemma kap_sq_eq (β : ℝ) (hb : 0 ≤ β) : 2 * kap β ^ 2 = F1 β := by
  unfold kap F1
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 1 + 12 * β by linarith)
  nlinarith [h]

lemma F1_quarter : F1 (1 / 4) = 1 / 2 := by
  rw [← kap_sq_eq _ (by norm_num), kap_quarter]; norm_num

lemma hasDerivAt_F1 (β : ℝ) (hb : 0 < 1 + 12 * β) :
    HasDerivAt F1 ((6 + 12 / (2 * Real.sqrt (1 + 12 * β))) / 9) β := by
  have h1 : HasDerivAt (fun y => 1 + 12 * y) 12 β := by
    simpa using ((hasDerivAt_id β).const_mul 12).const_add 1
  have h2 := h1.sqrt hb.ne'
  have h3 : HasDerivAt (fun y => 1 + 6 * y) 6 β := by
    simpa using ((hasDerivAt_id β).const_mul 6).const_add 1
  have h4 := (h3.add h2).div_const 9
  exact h4

lemma rho_eq_minG (β : ℝ) (hb : β1 ≤ β) : rho β = min (G β) 1 := by
  have hb0 : 0 ≤ β := by linarith [β1_bounds.1]
  unfold G
  rcases le_or_gt β (1 / 4) with h | h
  · rw [if_pos h, rho_of_le β hb0 h, ← kap_sq_eq β hb0]
    have hk1 : κ1 ≤ kap β := by rw [← kap_β1]; exact kap_mono hb
    have hk2 := kap_le β hb0 h
    have hk1' : 1 / 4 ≤ 2 * kap β ^ 2 := by nlinarith [κ1_sq, show 0 ≤ κ1 by unfold κ1; positivity]
    have hk0 := kap_ge β hb0
    rw [max_eq_right hk1', min_eq_left (by nlinarith)]
  · rw [if_neg (by linarith), rho_of_ge β h.le]

lemma G_cont : Continuous G := by
  unfold G
  apply Continuous.if_le (by unfold F1; fun_prop) Real.continuous_sqrt continuous_id continuous_const
  intro x hx; simp only [id] at hx; rw [hx, F1_quarter, sqrt_quarter]

lemma hasDerivAt_G (β : ℝ) (hb : 0 < β) : HasDerivAt G (G' β) β := by
  rcases lt_trichotomy β (1 / 4) with h | h | h
  · have hd := hasDerivAt_F1 β (by linarith)
    have : G =ᶠ[𝓝 β] F1 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      unfold G; rw [if_pos (le_of_lt hy)]
    unfold G'; rw [if_pos h.le]
    exact hd.congr_of_eventuallyEq this
  · subst h
    have hval : G' (1 / 4) = 1 := by
      unfold G'; rw [if_pos le_rfl]
      rw [show (1:ℝ) + 12 * (1 / 4) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
    rw [hval]
    have hd1 := hasDerivAt_F1 (1 / 4) (by norm_num)
    rw [show (1:ℝ) + 12 * (1 / 4) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at hd1
    norm_num at hd1
    have hd2 := Real.hasDerivAt_sqrt (show (1 / 4 : ℝ) ≠ 0 by norm_num)
    rw [sqrt_quarter] at hd2; norm_num at hd2
    have w1 : HasDerivWithinAt G 1 (Iic (1 / 4)) (1 / 4) := by
      apply hd1.hasDerivWithinAt.congr
      · intro y hy; unfold G; rw [if_pos (show y ≤ 1 / 4 from hy)]
      · unfold G; rw [if_pos le_rfl]
    have w2 : HasDerivWithinAt G 1 (Ici (1 / 4)) (1 / 4) := by
      apply hd2.hasDerivWithinAt.congr
      · intro y hy
        unfold G
        rcases eq_or_lt_of_le (show (1/4:ℝ) ≤ y from hy) with h' | h'
        · rw [← h', if_pos le_rfl, F1_quarter, sqrt_quarter]
        · rw [if_neg (by linarith)]
      · unfold G; rw [if_pos le_rfl, F1_quarter, sqrt_quarter]
    have := w1.union w2
    rw [Iic_union_Ici] at this
    exact this.hasDerivAt univ_mem
  · have hd := Real.hasDerivAt_sqrt (show β ≠ 0 by linarith)
    have : G =ᶠ[𝓝 β] Real.sqrt := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      unfold G; rw [if_neg (by simp only [mem_Ioi] at hy; linarith)]
    unfold G'; rw [if_neg (by linarith)]
    exact hd.congr_of_eventuallyEq this

lemma G'_strictAnti : StrictAntiOn G' (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  unfold G'
  rcases le_or_gt b (1 / 4) with hb4 | hb4
  · rw [if_pos hb4, if_pos (show a ≤ 1 / 4 by linarith)]
    have h1 := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 1 + 12 * a by linarith)
      (show 1 + 12 * a < 1 + 12 * b by linarith)
    have h0 : 0 < Real.sqrt (1 + 12 * a) := Real.sqrt_pos.mpr (by linarith)
    have : 12 / (2 * Real.sqrt (1 + 12 * b)) < 12 / (2 * Real.sqrt (1 + 12 * a)) := by
      apply div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)
    linarith
  · rw [if_neg (show ¬ (b ≤ 1 / 4) by linarith)]
    have hsb : 1 / 2 < Real.sqrt b := by
      rw [← sqrt_quarter]; exact Real.sqrt_lt_sqrt (by norm_num) hb4
    have hgb : 1 / (2 * Real.sqrt b) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    rcases le_or_gt a (1 / 4) with ha4 | ha4
    · rw [if_pos ha4]
      have h1 : Real.sqrt (1 + 12 * a) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; linarith
      have h0 : 0 < Real.sqrt (1 + 12 * a) := Real.sqrt_pos.mpr (by linarith)
      have : 3 ≤ 12 / (2 * Real.sqrt (1 + 12 * a)) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    · rw [if_neg (show ¬ (a ≤ 1 / 4) by linarith)]
      have h1 := Real.sqrt_lt_sqrt ha.le hab
      have h0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
      apply div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

lemma G_strictConcave : StrictConcaveOn ℝ (Ici β1) G := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici _) G_cont.continuousOn
  rw [interior_Ici]
  intro a ha b hb hab
  have ha' : β1 < a := ha
  have hb' : β1 < b := hb
  have hb1 := β1_bounds.1
  rw [(hasDerivAt_G a (by linarith)).deriv, (hasDerivAt_G b (by linarith)).deriv]
  exact G'_strictAnti (show a ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith)
    (show b ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith) hab

lemma rho_concave : ConcaveOn ℝ (Ici β1) rho := by
  have h := G_strictConcave.concaveOn.inf (concaveOn_const (c := (1:ℝ)) (convex_Ici β1))
  apply h.congr
  intro x hx
  simp only [Pi.inf_apply]
  rw [rho_eq_minG x hx]

lemma rho_strictConcave : StrictConcaveOn ℝ (Icc β1 1) rho := by
  have h := G_strictConcave.subset (Icc_subset_Ici_self : Icc β1 1 ⊆ Ici β1) (convex_Icc _ _)
  apply h.congr
  intro x hx
  rw [rho_eq_minG x hx.1]
  have hx0 : 0 ≤ x := by linarith [β1_bounds.1, hx.1]
  unfold G
  rcases le_or_gt x (1 / 4) with h4 | h4
  · rw [if_pos h4, min_eq_left]
    rw [← kap_sq_eq x hx0]; have := kap_le x hx0 h4; have := kap_ge x hx0; nlinarith
  · rw [if_neg (by linarith), min_eq_left]
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx.2

/-! slope lemmas -/

def Sl (a b : ℝ) : ℝ := (rho b - rho a) / (b - a)

lemma Sl_mul (a b : ℝ) (h : a < b) : Sl a b * (b - a) = rho b - rho a := by
  unfold Sl; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')

/-- three-point identity -/
lemma Sl_three (x y z : ℝ) (hxy : x < y) (hyz : y < z) :
    Sl x z * (z - x) = Sl x y * (y - x) + Sl y z * (z - y) := by
  rw [Sl_mul x z (by linarith), Sl_mul x y hxy, Sl_mul y z hyz]; ring

lemma rho_adj {x y z : ℝ} (hx : β1 ≤ x) (hxy : x < y) (hyz : y < z) : Sl y z ≤ Sl x y :=
  rho_concave.slope_anti_adjacent (show x ∈ Ici β1 from hx)
    (show z ∈ Ici β1 by simp only [mem_Ici]; linarith) hxy hyz

lemma rho_adj_strict {x y z : ℝ} (hx : β1 ≤ x) (hz : z ≤ 1) (hxy : x < y) (hyz : y < z) :
    Sl y z < Sl x y :=
  rho_strictConcave.slope_anti_adjacent (show x ∈ Icc β1 1 from ⟨hx, by linarith⟩)
    (show z ∈ Icc β1 1 from ⟨by linarith, hz⟩) hxy hyz

/-- fixed left endpoint: slope decreases as the right endpoint increases -/
lemma Sl_left {x y z : ℝ} (hx : β1 ≤ x) (hxy : x < y) (hyz : y ≤ z) : Sl x z ≤ Sl x y := by
  rcases eq_or_lt_of_le hyz with h | h
  · rw [h]
  · have h3 := Sl_three x y z hxy h
    have h4 := rho_adj hx hxy h
    have : Sl x z * (z - x) ≤ Sl x y * (z - x) := by nlinarith
    exact le_of_mul_le_mul_right this (by linarith)

lemma rho_pos_quarter (β : ℝ) (h : β1 < β) : 1 / 4 < rho β := by
  rcases le_or_gt β (1 / 4) with h4 | h4
  · have := rho_chord_β1 β h.le h4; linarith
  · rw [rho_of_ge β h4.le]
    have := sqrt_ge_half β h4.le
    exact lt_of_lt_of_le (by norm_num) (le_min this (by norm_num))

/-- strict decreasing differences of the perspective -/
lemma DD_strict {u u' v v' : ℝ} (hu : β1 < u) (hu1 : u < 1) (huu : u < u') (huv : u < v)
    (hvv : v < v') (huv' : u' < v') : Sl u' v' < Sl u v := by
  have hS1 : Sl u v' ≤ Sl u v := Sl_left hu.le huv hvv.le
  rcases lt_or_ge u' 1 with h1 | h1
  · -- S(u,u') > S(u',v')
    have key : Sl u' v' < Sl u u' := by
      rcases le_or_gt v' 1 with h2 | h2
      · exact rho_adj_strict hu.le h2 huu huv'
      · have a1 : Sl u' v' ≤ Sl u' 1 := Sl_left (by linarith) h1 h2.le
        have a2 : Sl u' 1 < Sl u u' := rho_adj_strict hu.le le_rfl huu h1
        linarith
    have h3 := Sl_three u u' v' huu huv'
    have : Sl u' v' * (v' - u) < Sl u v' * (v' - u) := by nlinarith
    have := lt_of_mul_lt_mul_right this (by linarith)
    linarith
  · have e1 : rho u' = 1 := by
      rw [rho_of_ge u' (by linarith), min_eq_right]
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
    have e2 : rho v' = 1 := by
      rw [rho_of_ge v' (by linarith), min_eq_right]
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hz : Sl u' v' = 0 := by unfold Sl; rw [e1, e2]; simp
    rw [hz]
    have hu0 : 0 ≤ u := by linarith [β1_bounds.1]
    have hr := rho_strict hu0 (show u < min v 1 from lt_min huv hu1) (min_le_right _ _)
      (rho_pos_quarter u hu)
    have hm := rho_mono (show 0 ≤ min v 1 by linarith [le_min huv.le hu1.le])
      (min_le_left v 1)
    unfold Sl
    apply div_pos (by linarith) (by linarith)

end

end ASP


namespace ASP

open Set Filter Topology ArtShortage.CashSubsidy

noncomputable section

section
variable (g : ℝ)

def q0 : ℝ := 1 / 2 - g / 8
def E (q : ℝ) : ℝ := q * (1 - q) + B g q / 4

lemma E_sq (q : ℝ) : E g q = E g (q0 g) - (q - q0 g) ^ 2 := by
  unfold E q0 B; ring

lemma TT_eq (b q : ℝ) : TT g b q = E g q + B g q * (rho (b / B g q) - 1 / 4) := by
  unfold TT E; ring

lemma B_pos (hg : 0 < g) (q : ℝ) (hq : q ≤ 1) : 1 ≤ B g q := by
  unfold B; nlinarith

lemma B0_eq : B g (q0 g) = (8 + 4 * g + g ^ 2) / 8 := by unfold B q0; ring

lemma TT_ge_E (hg : 0 < g) (b q : ℝ) (hb : 0 ≤ b) (hq : q ≤ 1) : E g q ≤ TT g b q := by
  rw [TT_eq]
  have h1 := B_pos g hg q hq
  have := rho_ge (b / B g q) (div_nonneg hb (by linarith))
  nlinarith

lemma TT_mono_b (hg : 0 < g) (b b' q : ℝ) (hb : 0 ≤ b) (hbb : b ≤ b') (hq : q ≤ 1) :
    TT g b q ≤ TT g b' q := by
  unfold TT
  have h1 := B_pos g hg q hq
  have := rho_mono (div_nonneg hb (by linarith)) (div_le_div_of_nonneg_right hbb (by linarith))
  nlinarith

lemma TT_contOn (hg : 0 < g) (b : ℝ) : ContinuousOn (TT g b) (Icc 0 1) := by
  unfold TT
  have hB : Continuous (B g) := by unfold B; fun_prop
  apply ContinuousOn.add (by fun_prop)
  apply ContinuousOn.mul hB.continuousOn
  apply rho_cont.comp_continuousOn
  apply continuousOn_const.div hB.continuousOn
  intro x hx; have := B_pos g hg x hx.2; linarith

lemma TT_cont_b (q : ℝ) : Continuous (fun b => TT g b q) := by
  unfold TT
  have := rho_cont
  fun_prop

end

/-! ### main analysis -/

section
variable (g : ℝ) (hg : 0 < g) (hg4 : g < 4)
include hg hg4

lemma q0_mem : q0 g ∈ Icc (0:ℝ) 1 := by unfold q0; constructor <;> linarith

lemma small_b (b : ℝ) (hb : 0 ≤ b) (hb64 : b ≤ 1 / 64) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (hne : q ≠ q0 g) : TT g b q < TT g b (q0 g) := by
  have hq0 := q0_mem g hg hg4
  rw [TT_eq, TT_eq]
  have h1 := B_pos g hg q hq.2
  have h2 := B_pos g hg (q0 g) hq0.2
  have r1 : rho (b / B g q) = 1 / 4 := rho_small _ (div_nonneg hb (by linarith))
    (le_trans (div_le_self hb h1) hb64)
  have r2 : rho (b / B g (q0 g)) = 1 / 4 := rho_small _ (div_nonneg hb (by linarith))
    (le_trans (div_le_self hb h2) hb64)
  rw [r1, r2, E_sq g q]
  have : 0 < (q - q0 g) ^ 2 := by
    have : q - q0 g ≠ 0 := sub_ne_zero.mpr hne
    positivity
  linarith

lemma bR_witness : ∃ q ∈ Icc (0:ℝ) 1, q ≠ q0 g ∧
    TT g (β1 * B g (q0 g)) (q0 g) < TT g (β1 * B g (q0 g)) q := by
  obtain ⟨hb1, hb4⟩ := β1_bounds
  have hb40 : β1 < 1 / 40 := by unfold β1; rw [κ1_sq]; unfold κ1; linarith [sqrt2_bounds.1]
  set B0 := B g (q0 g) with hB0
  have hB0v : B0 = (8 + 4 * g + g ^ 2) / 8 := B0_eq g
  have hB01 : 1 ≤ B0 := by rw [hB0v]; nlinarith
  set δ := β1 * g / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ < 1 / 10 := by rw [hδ]; nlinarith
  set q := q0 g + δ
  have hq : q ∈ Icc (0:ℝ) 1 := by
    constructor
    · have := (q0_mem g hg hg4).1; linarith
    · unfold q0 at *; simp only [q]; unfold q0; linarith
  refine ⟨q, hq, by simp only [q]; linarith, ?_⟩
  have hBq : B g q = B0 - g * δ := by rw [hB0]; simp only [q]; unfold B; ring
  have hgδ : g * δ < 8 * β1 := by rw [hδ]; nlinarith
  have hBq1 : 1 ≤ B g q := B_pos g hg q hq.2
  set bR := β1 * B0
  have hβq1 : β1 ≤ bR / B g q := by
    rw [le_div_iff₀ (by linarith), hBq]; simp only [bR]; nlinarith
  have hβq4 : bR / B g q ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith), hBq]; simp only [bR]
    nlinarith [mul_le_mul_of_nonneg_right hB01 (show (0:ℝ) ≤ 1 - 4 * β1 by linarith)]
  have hchord := rho_chord_β1 _ hβq1 hβq4
  have hrho0 : rho (bR / B0) = 1 / 4 := by
    simp only [bR]; rw [mul_div_assoc, div_self (by linarith), mul_one]; exact rho_β1
  rw [TT_eq, TT_eq, hrho0, E_sq g q]
  have e1 : B g q * (bR / B g q - β1) = bR - β1 * B g q := by field_simp
  have : B g q * (1 / 4 + (bR / B g q - β1) - 1 / 4) ≤ B g q * (rho (bR / B g q) - 1 / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hqq : q - q0 g = δ := by simp only [q]; ring
  rw [hqq]
  have e2 : bR - β1 * B g q = β1 * g * δ := by rw [hBq]; simp only [bR]; ring
  nlinarith

lemma left_lt (b : ℝ) (hb : 0 ≤ b) (hbb : b ≤ B g (q0 g) / 4) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (hlt : q < q0 g) : TT g b q < TT g b (q0 g) := by
  have hq0 := q0_mem g hg hg4
  rw [TT_eq, TT_eq, E_sq g q]
  set B0 := B g (q0 g)
  have h1 := B_pos g hg q hq.2
  have h2 := B_pos g hg (q0 g) hq0.2
  have hBB : B0 < B g q := by simp only [B0]; unfold B; nlinarith
  have key : B g q * (rho (b / B g q) - 1 / 4) ≤ B0 * (rho (b / B0) - 1 / 4) := by
    rcases eq_or_lt_of_le hb with h0 | h0
    · rw [← h0]; simp [rho_small 0 le_rfl (by norm_num)]
    · have hm := phi_mono_low (b / B g q) (b / B0) (div_pos h0 (by linarith))
        (div_le_div_of_nonneg_left hb (by linarith) hBB.le)
        (by rw [div_le_iff₀ (by linarith)]; linarith)
      -- multiply by B * B0 / b
      have hB0ne : B0 ≠ 0 := by simp only [B0]; linarith
      have hBqne : B g q ≠ 0 := by linarith
      have hpos : 0 < B g q * B0 / b := by positivity
      have := mul_le_mul_of_nonneg_left hm hpos.le
      have e1 : B g q * B0 / b * (b / B0 * (rho (b / B g q) - 1 / 4)) =
          B g q * (rho (b / B g q) - 1 / 4) := by field_simp
      have e2 : B g q * B0 / b * (b / B g q * (rho (b / B0) - 1 / 4)) =
          B0 * (rho (b / B0) - 1 / 4) := by field_simp
      linarith
  have : 0 < (q - q0 g) ^ 2 := by
    have : q - q0 g ≠ 0 := by linarith
    positivity
  linarith

lemma right_le (b : ℝ) (hbb : B g (q0 g) / 4 ≤ b) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (hge : q0 g ≤ q) : TT g b q ≤ TT g b (q0 g) := by
  have hq0 := q0_mem g hg hg4
  rw [TT_eq, TT_eq, E_sq g q]
  set B0 := B g (q0 g)
  have h1 := B_pos g hg q hq.2
  have h2 := B_pos g hg (q0 g) hq0.2
  have hb : 0 < b := by linarith
  have hBB : B g q ≤ B0 := by simp only [B0]; unfold B; nlinarith
  have key : B g q * (rho (b / B g q) - 1 / 4) ≤ B0 * (rho (b / B0) - 1 / 4) := by
    have hm := phi_anti_high (b / B0) (b / B g q)
      (by rw [le_div_iff₀ (by linarith)]; linarith)
      (div_le_div_of_nonneg_left hb.le (by linarith) hBB)
    have hB0ne : B0 ≠ 0 := by simp only [B0]; linarith
    have hBqne : B g q ≠ 0 := by linarith
    have hpos : 0 < B g q * B0 / b := by positivity
    have := mul_le_mul_of_nonneg_left hm hpos.le
    have e1 : B g q * B0 / b * (b / B0 * (rho (b / B g q) - 1 / 4)) =
        B g q * (rho (b / B g q) - 1 / 4) := by field_simp
    have e2 : B g q * B0 / b * (b / B g q * (rho (b / B0) - 1 / 4)) =
        B0 * (rho (b / B0) - 1 / 4) := by field_simp
    linarith
  nlinarith [sq_nonneg (q - q0 g)]

lemma left_better (b : ℝ) (hbb : B g (q0 g) / 4 < b) :
    ∃ q ∈ Icc (0:ℝ) 1, q < q0 g ∧ TT g b (q0 g) < TT g b q := by
  have hq0 := q0_mem g hg hg4
  set B0 := B g (q0 g) with hB0
  have h2 := B_pos g hg (q0 g) hq0.2
  have hb : 0 < b := by linarith
  set β0 := b / B0
  have hβ0 : 1 / 4 < β0 := by simp only [β0]; rw [lt_div_iff₀ (by linarith)]; linarith
  set m := Sl (1 / 4) β0
  have hm1 : m < 1 := by
    simp only [m]; unfold Sl
    rw [div_lt_one (by linarith), rho_of_ge β0 hβ0.le, rho_of_ge (1/4) le_rfl, sqrt_quarter]
    rcases le_or_gt β0 1 with h1 | h1
    · have hs1 : Real.sqrt β0 ≤ 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
      rw [min_eq_left hs1, min_eq_left (by norm_num)]
      have hs : 1 / 2 < Real.sqrt β0 := by
        rw [← sqrt_quarter]; exact Real.sqrt_lt_sqrt (by norm_num) hβ0
      have := Real.sq_sqrt (show (0:ℝ) ≤ β0 by linarith)
      nlinarith
    · rw [min_eq_right, min_eq_left (by norm_num)]
      · linarith
      · rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le
  have hq00 : 0 < q0 g := by unfold q0; linarith
  set δ := min (q0 g) (min ((4 * b - B0) / g) (g * (1 - m) / 8)) with hδ
  have hδ0 : 0 < δ := by
    apply lt_min hq00 (lt_min (div_pos (by linarith) hg) (by nlinarith))
  have hδ1 : δ ≤ q0 g := min_le_left _ _
  have hδ2 : δ ≤ (4 * b - B0) / g := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : δ ≤ g * (1 - m) / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  set q := q0 g - δ
  have hq : q ∈ Icc (0:ℝ) 1 := ⟨by simp only [q]; linarith, by simp only [q]; linarith [hq0.2]⟩
  refine ⟨q, hq, by simp only [q]; linarith, ?_⟩
  have hBq : B g q = B0 + g * δ := by rw [hB0]; simp only [q]; unfold B; ring
  have hgδ : g * δ ≤ 4 * b - B0 := by
    have := mul_le_mul_of_nonneg_left hδ2 hg.le
    rwa [mul_div_cancel₀ _ hg.ne'] at this
  have hBq1 : 0 < B g q := by rw [hBq]; nlinarith
  set β' := b / B g q
  have hβ'1 : 1 / 4 ≤ β' := by simp only [β']; rw [le_div_iff₀ hBq1]; linarith
  have hβ'2 : β' ≤ β0 := by
    simp only [β', β0]; apply div_le_div_of_nonneg_left hb.le (by linarith); rw [hBq]; nlinarith
  -- chord inequality
  have hchord : rho (1 / 4) + m * (β' - 1 / 4) ≤ rho β' := by
    rcases eq_or_lt_of_le hβ'1 with h | h
    · rw [← h]; simp
    · have hS := Sl_left (show β1 ≤ 1 / 4 by linarith [β1_bounds.2]) h hβ'2
      have e := Sl_mul (1 / 4) β' h
      have : Sl (1/4) β0 * (β' - 1 / 4) ≤ Sl (1/4) β' * (β' - 1 / 4) :=
        mul_le_mul_of_nonneg_right hS (by linarith)
      simp only [m]; linarith
  have hr0 : rho β0 = rho (1 / 4) + m * (β0 - 1 / 4) := by
    have := Sl_mul (1 / 4) β0 hβ0; simp only [m]; linarith
  rw [rho_of_ge (1/4) le_rfl, sqrt_quarter, min_eq_left (by norm_num)] at hchord hr0
  unfold TT
  have e1 : B g q * β' = b := by simp only [β']; field_simp
  have hB0ne : B0 ≠ 0 := by rw [hB0]; linarith
  have e2 : B0 * β0 = b := by simp only [β0]; field_simp
  have h3 : B g q * (1 / 2 + m * (β' - 1 / 4)) ≤ B g q * rho β' :=
    mul_le_mul_of_nonneg_left hchord hBq1.le
  have hgm : 0 < g * (1 - m) := by nlinarith
  have hqv : q * (1 - q) = q0 g * (1 - q0 g) - δ * (g / 4) - δ ^ 2 := by
    simp only [q]; unfold q0; ring
  rw [hr0, hqv]
  change q0 g * (1 - q0 g) + B0 * (1 / 2 + m * (β0 - 1 / 4)) <
    q0 g * (1 - q0 g) - δ * (g / 4) - δ ^ 2 + B g q * rho β'
  have : δ * (g * (1 - m) / 4 - δ) > 0 := mul_pos hδ0 (by nlinarith)
  nlinarith

end

end

end ASP


namespace ASP

open Set Filter Topology ArtShortage.CashSubsidy

noncomputable section

section
variable (g : ℝ) (hg : 0 < g) (hg4 : g < 4)
include hg hg4

lemma M1_core (b b'' q q'' : ℝ) (hb'' : 0 ≤ b'') (hlt : b'' < b) (hq'' : q'' ∈ Icc (0:ℝ) 1)
    (hne'' : q'' ≠ q0 g) (h'' : TT g b'' (q0 g) ≤ TT g b'' q'') (hq : q ∈ Icc (0:ℝ) 1)
    (hmax : ∀ q' ∈ Icc (0:ℝ) 1, TT g b q' ≤ TT g b q) (hr : rho (b / B g q) = 1 / 4) : False := by
  have hq0 := q0_mem g hg hg4
  have hb : 0 ≤ b := by linarith
  have hBq := B_pos g hg q hq.2
  have hB0 := B_pos g hg (q0 g) hq0.2
  have hB'' := B_pos g hg q'' hq''.2
  -- q = q0
  have e1 : TT g b q = E g (q0 g) - (q - q0 g) ^ 2 := by
    rw [TT_eq, hr, E_sq g q]; ring
  have e2 := TT_ge_E g hg b (q0 g) hb hq0.2
  have h3 := hmax (q0 g) hq0
  have hsq : (q - q0 g) ^ 2 = 0 := by nlinarith [sq_nonneg (q - q0 g)]
  have hqq : q = q0 g := by nlinarith [sq_nonneg (q - q0 g)]
  have hT0 : TT g b (q0 g) = E g (q0 g) :=
    le_antisymm (by nlinarith [sq_nonneg (q - q0 g)]) e2
  have hr0 : rho (b / B g (q0 g)) = 1 / 4 := by rw [hqq] at hr; exact hr
  have hbsmall := rho_eq_quarter_lt _ (div_nonneg hb (by linarith)) hr0
  have hb1 : b < 1 := by
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < B g (q0 g))).mp hbsmall
    have : B g (q0 g) ≤ 1 + g := by unfold B q0; nlinarith
    linarith
  -- chain
  have c1 := TT_mono_b g hg b'' b q'' hb'' hlt.le hq''.2
  have c2 := TT_ge_E g hg b'' (q0 g) hb'' hq0.2
  have c3 := hmax q'' hq''
  rw [hqq] at c3
  have eq1 : TT g b q'' = TT g b'' q'' := by linarith
  have eq2 : TT g b'' q'' = E g (q0 g) := by linarith
  rw [TT_eq, E_sq g q''] at eq2
  have hpos : 0 < (q'' - q0 g) ^ 2 := by
    have : q'' - q0 g ≠ 0 := sub_ne_zero.mpr hne''
    positivity
  have hrho'' : 1 / 4 < rho (b'' / B g q'') := by
    by_contra hc; push Not at hc
    have : B g q'' * (rho (b'' / B g q'') - 1 / 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  have hst := rho_strict (div_nonneg hb'' (by linarith))
    (div_lt_div_of_pos_right hlt (by linarith))
    (by rw [div_le_one (by linarith)]; linarith) hrho''
  unfold TT at eq1
  have : B g q'' * rho (b'' / B g q'') < B g q'' * rho (b / B g q'') :=
    mul_lt_mul_of_pos_left hst (by linarith)
  linarith

lemma DD_core (b b' q q' : ℝ) (hb0 : 0 < b) (hbb : b < b') (hq : q ∈ Icc (0:ℝ) 1)
    (hq' : q' ∈ Icc (0:ℝ) 1) (hqq : q < q')
    (hmax : ∀ x ∈ Icc (0:ℝ) 1, TT g b x ≤ TT g b q)
    (hmax' : ∀ x ∈ Icc (0:ℝ) 1, TT g b' x ≤ TT g b' q')
    (hu : β1 < b / B g q) : False := by
  have hBq := B_pos g hg q hq.2
  have hBq' := B_pos g hg q' hq'.2
  have hBB : B g q' < B g q := by unfold B; nlinarith
  set u := b / B g q
  set v := b' / B g q
  set u' := b / B g q'
  set v' := b' / B g q'
  have h1 := hmax q' hq'
  have h2 := hmax' q hq
  -- the two increments
  have eD : TT g b' q - TT g b q = Sl u v * (b' - b) := by
    have huv : u < v := div_lt_div_of_pos_right hbb (by linarith)
    have := Sl_mul u v huv
    have e : B g q * (v - u) = b' - b := by simp only [u, v]; field_simp
    unfold TT
    calc _ = B g q * (rho v - rho u) := by simp only [u, v]; ring
      _ = B g q * (Sl u v * (v - u)) := by rw [this]
      _ = Sl u v * (B g q * (v - u)) := by ring
      _ = _ := by rw [e]
  have eD' : TT g b' q' - TT g b q' = Sl u' v' * (b' - b) := by
    have huv : u' < v' := div_lt_div_of_pos_right hbb (by linarith)
    have := Sl_mul u' v' huv
    have e : B g q' * (v' - u') = b' - b := by simp only [u', v']; field_simp
    unfold TT
    calc _ = B g q' * (rho v' - rho u') := by simp only [u', v']; ring
      _ = B g q' * (Sl u' v' * (v' - u')) := by rw [this]
      _ = Sl u' v' * (B g q' * (v' - u')) := by ring
      _ = _ := by rw [e]
  have hge : Sl u v * (b' - b) ≤ Sl u' v' * (b' - b) := by linarith
  have hge' : Sl u v ≤ Sl u' v' := le_of_mul_le_mul_right hge (by linarith)
  rcases lt_or_ge u 1 with hu1 | hu1
  · have := DD_strict hu hu1 (div_lt_div_of_pos_left hb0 (by linarith) hBB)
      (div_lt_div_of_pos_right hbb (by linarith))
      (div_lt_div_of_pos_left (by linarith) (by linarith) hBB)
      (div_lt_div_of_pos_right hbb (by linarith))
    linarith
  · -- regime IV on [q, q']: midpoint contradiction
    have hrho1 : ∀ x ∈ Icc q q', rho (b / B g x) = 1 := by
      intro x hx
      have hBx := B_pos g hg x (le_trans hx.2 hq'.2)
      have hBxq : B g x ≤ B g q := by unfold B; nlinarith [hx.1]
      have : 1 ≤ b / B g x := le_trans hu1 (div_le_div_of_nonneg_left hb0.le (by linarith) hBxq)
      rw [rho_of_ge _ (by linarith), min_eq_right]
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt this
    have hrho1' : ∀ x ∈ Icc q q', rho (b' / B g x) = 1 := by
      intro x hx
      have hBx := B_pos g hg x (le_trans hx.2 hq'.2)
      have hBxq : B g x ≤ B g q := by unfold B; nlinarith [hx.1]
      have : 1 ≤ b' / B g x := le_trans hu1 (le_trans (div_le_div_of_nonneg_left hb0.le
        (by linarith) hBxq) (div_le_div_of_nonneg_right hbb.le (by linarith)))
      rw [rho_of_ge _ (by linarith), min_eq_right]
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt this
    have a1 := hrho1 q ⟨le_rfl, hqq.le⟩
    have a2 := hrho1 q' ⟨hqq.le, le_rfl⟩
    have a3 := hrho1' q ⟨le_rfl, hqq.le⟩
    have a4 := hrho1' q' ⟨hqq.le, le_rfl⟩
    have heq : TT g b q' = TT g b q := by
      unfold TT at h1 h2 ⊢; rw [a1, a2] at h1; rw [a3, a4] at h2; rw [a1, a2]; linarith
    set m := (q + q') / 2
    have hm : m ∈ Icc q q' := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
    have hm01 : m ∈ Icc (0:ℝ) 1 := ⟨by linarith [hq.1, hm.1], by linarith [hq'.2, hm.2]⟩
    have a5 := hrho1 m hm
    have h3 := hmax m hm01
    unfold TT at h3 heq
    rw [a5, a1] at h3; rw [a1, a2] at heq
    have hBm : B g m = (B g q + B g q') / 2 := by simp only [m]; unfold B; ring
    have hconc : (q * (1 - q) + q' * (1 - q')) / 2 < m * (1 - m) := by
      simp only [m]; nlinarith [sq_pos_of_pos (show 0 < q' - q by linarith)]
    nlinarith

end

end

end ASP


open Set Filter Topology ArtShortage.CashSubsidy ASP

theorem solution (g lam : ℝ) (hS : Standing g lam) :
    (∀ b, 0 ≤ b → (EqQ1 g lam b).Nonempty) ∧
    ∃ t1 : ℝ, 0 < t1 ∧ t1 < (8 + 4 * g + g^2) / 32 ∧
      -- (i)(a) and (ii)(a)
      (∀ b, 0 ≤ b → b < t1 → EqQ1 g lam b = {1/2 - g/8}) ∧
      (1/2 - g/8) ∈ EqQ1 g lam t1 ∧
      -- (i)(b)
      (∀ b, t1 < b → b ≤ (8 + 4 * g + g^2) / 32 → ∀ q ∈ EqQ1 g lam b, 1/2 - g/8 ≤ q) ∧
      -- (i)(c)
      (∀ b, (8 + 4 * g + g^2) / 32 < b → ∀ q ∈ EqQ1 g lam b, q < 1/2 - g/8) ∧
      -- (ii)(b)
      (∀ b b', t1 < b → b < b' → ∀ q ∈ EqQ1 g lam b, ∀ q' ∈ EqQ1 g lam b', q' ≤ q) := by
  obtain ⟨hg, hg4, hl⟩ := hS
  have hS' : Standing g lam := ⟨hg, hg4, hl⟩
  have hq0e : (1 / 2 - g / 8 : ℝ) = q0 g := rfl
  have hq0 := q0_mem g hg hg4
  have hbbar : (8 + 4 * g + g ^ 2) / 32 = B g (q0 g) / 4 := by rw [B0_eq]; ring
  have hB0 := B_pos g hg (q0 g) hq0.2
  have mem_iff : ∀ b, 0 ≤ b → ∀ q, q ∈ EqQ1 g lam b ↔
      (q ∈ Icc (0:ℝ) 1 ∧ ∀ q' ∈ Icc (0:ℝ) 1, TT g b q' ≤ TT g b q) := by
    intro b hb q; rw [EqQ1_char g lam b hS' hb]; rfl
  rw [hq0e, hbbar]
  -- the set S and t1
  set S : Set ℝ := {b | 0 ≤ b ∧ ∃ q ∈ Icc (0:ℝ) 1, q ≠ q0 g ∧ TT g b (q0 g) ≤ TT g b q} with hSdef
  obtain ⟨qR, hqR, hneR, hltR⟩ := bR_witness g hg hg4
  have hbR0 : 0 ≤ β1 * B g (q0 g) := by have := β1_bounds.1; positivity
  have hbRS : β1 * B g (q0 g) ∈ S := ⟨hbR0, qR, hqR, hneR, hltR.le⟩
  have hSlow : ∀ b ∈ S, 1 / 64 < b := by
    rintro b ⟨hb, q, hq, hne, hle⟩
    by_contra hc; push Not at hc
    have := small_b g hg hg4 b hb hc q hq hne
    linarith
  have hbdd : BddBelow S := ⟨0, fun b hb => hb.1⟩
  have hne : S.Nonempty := ⟨_, hbRS⟩
  set t1 := sInf S with ht1
  have ht1low : 1 / 64 ≤ t1 := le_csInf hne (fun b hb => (hSlow b hb).le)
  have ht1R : t1 ≤ β1 * B g (q0 g) := csInf_le hbdd hbRS
  have ht1pos : 0 < t1 := by linarith
  have hnotS : ∀ b, 0 ≤ b → b < t1 → ∀ q ∈ Icc (0:ℝ) 1, q ≠ q0 g → TT g b q < TT g b (q0 g) := by
    intro b hb hbt q hq hqne
    by_contra hc; push Not at hc
    have : b ∈ S := ⟨hb, q, hq, hqne, hc⟩
    have := csInf_le hbdd this
    linarith
  refine ⟨?_, t1, ht1pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty
    intro b hb
    obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one)
      (TT_contOn g hg b)
    exact ⟨q, (mem_iff b hb q).mpr ⟨hq, fun q' hq' => hmax hq'⟩⟩
  · -- t1 < bbar
    have := β1_bounds.2
    nlinarith
  · -- (i)(a)
    intro b hb hbt
    ext q
    rw [mem_iff b hb q, mem_singleton_iff]
    constructor
    · rintro ⟨hq, hmax⟩
      by_contra hqne
      have := hnotS b hb hbt q hq hqne
      have := hmax (q0 g) hq0
      linarith
    · rintro rfl
      refine ⟨hq0, fun q' hq' => ?_⟩
      by_cases h : q' = q0 g
      · rw [h]
      · exact (hnotS b hb hbt q' hq' h).le
  · -- q0 ∈ EqQ1 t1
    rw [mem_iff t1 ht1pos.le]
    refine ⟨hq0, fun q' hq' => ?_⟩
    by_contra hc; push Not at hc
    have hcont : Continuous (fun b => TT g b q' - TT g b (q0 g)) :=
      (TT_cont_b g q').sub (TT_cont_b g (q0 g))
    have hpos : 0 < TT g t1 q' - TT g t1 (q0 g) := by linarith
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (hcont.continuousAt.eventually (lt_mem_nhds hpos))
    set b := max 0 (t1 - ε / 2)
    have hb0 : 0 ≤ b := le_max_left _ _
    have hbt : b < t1 := max_lt ht1pos (by linarith)
    have hdist : dist b t1 < ε := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
      have : t1 - ε / 2 ≤ b := le_max_right _ _
      linarith
    have := hball hdist
    have hqne : q' ≠ q0 g := by
      intro h; rw [h] at this; simp at this
    have := hnotS b hb0 hbt q' hq' hqne
    linarith
  · -- (i)(b)
    intro b hbt hbb q hq
    have hb : 0 ≤ b := by linarith
    obtain ⟨hq, hmax⟩ := (mem_iff b hb q).mp hq
    by_contra hc; push Not at hc
    have := left_lt g hg hg4 b hb hbb q hq hc
    have := hmax (q0 g) hq0
    linarith
  · -- (i)(c)
    intro b hbb q hq
    have hb : 0 ≤ b := by linarith
    obtain ⟨hq, hmax⟩ := (mem_iff b hb q).mp hq
    by_contra hc; push Not at hc
    have h1 := right_le g hg hg4 b hbb.le q hq hc
    obtain ⟨q'', hq'', -, h2⟩ := left_better g hg hg4 b hbb
    have := hmax q'' hq''
    linarith
  · -- (ii)(b)
    intro b b' hbt hbb q hq q' hq'
    have hb : 0 < b := by linarith
    obtain ⟨hq, hmax⟩ := (mem_iff b hb.le q).mp hq
    obtain ⟨hq', hmax'⟩ := (mem_iff b' (by linarith) q').mp hq'
    by_contra hc; push Not at hc
    -- maximizers at b lie beyond β1
    have hu : β1 < b / B g q := by
      apply rho_gt_quarter_imp _ (div_nonneg hb.le (by linarith [B_pos g hg q hq.2]))
      rcases eq_or_lt_of_le (rho_ge (b / B g q) (div_nonneg hb.le
        (by linarith [B_pos g hg q hq.2]))) with h | h
      · exfalso
        obtain ⟨b'', hb''S, hb''lt⟩ := exists_lt_of_csInf_lt hne hbt
        obtain ⟨hb'', q'', hq'', hne'', h''⟩ := hb''S
        exact M1_core g hg hg4 b b'' q q'' hb'' hb''lt hq'' hne'' h'' hq hmax h.symm
      · exact h
    exact DD_core g hg hg4 b b' q q' hb hbb hq hq' hc hmax hmax' hu


