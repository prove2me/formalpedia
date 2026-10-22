-- Prove2me | solution 1 for AdvanceSales.Pricing.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T19:56:53.058261+00:00
-- url     : https://prove2.me/submissions/92cd3c68-0c18-4b5f-9c78-387510d5bb27

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

set_option autoImplicit false

namespace AS4Aux
open AdvanceSales.Pricing

lemma prof_le (B y : ℝ) (hB : 0 < B) :
    B * (1 - Real.exp (-y)) - y ≤ B - 1 - Real.log B := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hB (Real.exp_pos (-y)))
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

lemma exp_tan (u w : ℝ) : Real.exp w * (1 + (u - w)) ≤ Real.exp u := by
  have h := Real.add_one_le_exp (u - w)
  have h2 : Real.exp u = Real.exp w * Real.exp (u - w) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos w).le

lemma one_sub_exp_lt (x : ℝ) (hx : 0 < x) : 0 < 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) < x := by
  constructor
  · have := Real.exp_lt_exp.2 (by linarith : -x < 0)
    rw [Real.exp_zero] at this
    linarith
  · have := Real.add_one_lt_exp (by linarith : -x ≠ 0)
    linarith

lemma W_spec (k : ℝ) (hk : 0 < k) :
    -1 < Wk k ∧ Wk k < 0 ∧ Wk k * Real.exp (Wk k) = -(k + 1) * Real.exp (-(k + 1)) := by
  have hlt : (k + 1) * Real.exp (-(k + 1)) < Real.exp (-1) := by
    have h1 : k + 1 < Real.exp k := by
      have := Real.add_one_lt_exp hk.ne'; linarith
    have h2 : Real.exp (-1) = Real.exp k * Real.exp (-(k + 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]; exact mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
  have hcneg : -(k + 1) * Real.exp (-(k + 1)) < 0 := by
    have := Real.exp_pos (-(k + 1)); nlinarith
  have hex : ∃ w : ℝ, -1 ≤ w ∧ w * Real.exp w = -(k + 1) * Real.exp (-(k + 1)) := by
    have hcont : ContinuousOn (fun w : ℝ => w * Real.exp w) (Set.Icc (-1) 0) := by fun_prop
    have hmem : -(k + 1) * Real.exp (-(k + 1)) ∈
        Set.Icc ((fun w : ℝ => w * Real.exp w) (-1)) ((fun w : ℝ => w * Real.exp w) 0) := by
      simp only [Set.mem_Icc, zero_mul]
      constructor <;> linarith
    obtain ⟨w, hw, hw2⟩ := intermediate_value_Icc (by norm_num) hcont hmem
    exact ⟨w, hw.1, hw2⟩
  have hW : Wk k = Classical.choose hex := by
    unfold Wk lambertW; rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  rw [← hW] at hs
  obtain ⟨h1, h2⟩ := hs
  have hneg : Wk k < 0 := by
    by_contra h; push Not at h
    have := mul_nonneg h (Real.exp_pos (Wk k)).le; linarith
  refine ⟨?_, hneg, h2⟩
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso; rw [← h] at h2; linarith

lemma keyW (k : ℝ) (hk : 0 < k) :
    Real.exp (-(Wk k + k + 1)) * (k + 1) = -Wk k := by
  obtain ⟨_, _, h⟩ := W_spec k hk
  have e : Real.exp (-(Wk k + k + 1)) = Real.exp (-Wk k) * Real.exp (-(k + 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have h3 : Real.exp (-Wk k) * Real.exp (Wk k) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (Real.exp (-Wk k)) * h - (Wk k) * h3

lemma hys (k : ℝ) (hk : 0 < k) :
    (k + 1) * (1 - Real.exp (-(Wk k + k + 1))) = Wk k + k + 1 := by
  have := keyW k hk; linarith

lemma T_le (k T : ℝ) (hk : 0 < k) (h : T ≤ (k + 1) * (1 - Real.exp (-T))) :
    T ≤ Wk k + k + 1 := by
  obtain ⟨hW1, hW2, _⟩ := W_spec k hk
  have hK := keyW k hk
  have h1 := exp_tan (-T) (-(Wk k + k + 1))
  have h2 : (k + 1) * (Real.exp (-(Wk k + k + 1)) * (1 + (-T - -(Wk k + k + 1))))
      ≤ (k + 1) * Real.exp (-T) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : (k + 1) * (Real.exp (-(Wk k + k + 1)) * (1 + (-T - -(Wk k + k + 1))))
      = -Wk k * (1 + (Wk k + k + 1 - T)) := by
    rw [← hK]; ring
  rw [h3] at h2
  by_contra hc; push Not at hc
  have := mul_pos (sub_pos.2 hc) (by linarith : (0:ℝ) < 1 + Wk k)
  linarith

lemma psi_nonneg (k L : ℝ) (hk : 0 < k) (h0 : 0 ≤ L) (hL : L ≤ Wk k + k + 1) :
    L ≤ (k + 1) * (1 - Real.exp (-L)) := by
  obtain ⟨hW1, hW2, _⟩ := W_spec k hk
  have hY := hys k hk
  have hy0 : 0 < Wk k + k + 1 := by linarith
  have hYne : Wk k + k + 1 ≠ 0 := hy0.ne'
  have ht0 : 0 ≤ L / (Wk k + k + 1) := div_nonneg h0 hy0.le
  have ht1 : L / (Wk k + k + 1) ≤ 1 := (div_le_one hy0).2 hL
  have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-(Wk k + k + 1)))
    (sub_nonneg.2 ht1) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have e1 : L / (Wk k + k + 1) * -(Wk k + k + 1) = -L := by field_simp
  rw [e1] at hc
  have e2 : (k + 1) * (L / (Wk k + k + 1) * (1 - Real.exp (-(Wk k + k + 1)))) = L := by
    calc (k + 1) * (L / (Wk k + k + 1) * (1 - Real.exp (-(Wk k + k + 1))))
        = L / (Wk k + k + 1) * ((k + 1) * (1 - Real.exp (-(Wk k + k + 1)))) := by ring
      _ = L := by rw [hY]; field_simp
  have hm := mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ k + 1)
  linarith

lemma f_nonpos (k V v : ℝ) (hk : 0 < k) (hV : k + 1 < V) (hfV : f k V = 0)
    (h1 : k + 1 ≤ v) (h2 : v ≤ V) : f k v ≤ 0 := by
  unfold f at *
  have hVa : 0 < V - (k + 1) := by linarith
  have hk1 : (k + 1) ≠ 0 := by linarith
  set t := (v - (k + 1)) / (V - (k + 1)) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hVa.le
  have ht1 : t ≤ 1 := (div_le_one hVa).2 (by linarith)
  have htV : t * (V - (k + 1)) = v - (k + 1) := by rw [ht]; field_simp
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (by norm_num : (0:ℝ) < 1))
    (Set.mem_Ioi.2 (by linarith : (0:ℝ) < V - k)) (sub_nonneg.2 ht1) ht0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  have e : (1 - t) + t * (V - k) = v - k := by linarith [htV]
  rw [e] at hc
  have h0 : (1 - v / (k + 1)) - t * (1 - V / (k + 1)) = 0 := by
    rw [show (1 - v / (k + 1)) - t * (1 - V / (k + 1))
        = (t * (V - (k + 1)) - (v - (k + 1))) / (k + 1) by field_simp; ring, htV, sub_self,
      zero_div]
  have lin : (1 - v / (k + 1)) * Wk k = t * ((1 - V / (k + 1)) * Wk k) := by
    linear_combination (Wk k) * h0
  calc (1 - v / (k + 1)) * Wk k - Real.log (v - k)
      = t * ((1 - V / (k + 1)) * Wk k - Real.log (V - k))
          + (t * Real.log (V - k) - Real.log (v - k)) := by rw [lin]; ring
    _ = t * 0 + (t * Real.log (V - k) - Real.log (v - k)) := by rw [hfV]
    _ ≤ 0 := by linarith

lemma f_nonneg (k V v : ℝ) (hk : 0 < k) (hV : k + 1 < V) (hfV : f k V = 0)
    (h : V ≤ v) : 0 ≤ f k v := by
  unfold f at *
  have hva : 0 < v - (k + 1) := by linarith
  have hk1 : (k + 1) ≠ 0 := by linarith
  set t := (V - (k + 1)) / (v - (k + 1)) with ht
  have ht0 : 0 < t := div_pos (by linarith) hva
  have ht1 : t ≤ 1 := (div_le_one hva).2 (by linarith)
  have htv : t * (v - (k + 1)) = V - (k + 1) := by rw [ht]; field_simp
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (by norm_num : (0:ℝ) < 1))
    (Set.mem_Ioi.2 (by linarith : (0:ℝ) < v - k)) (sub_nonneg.2 ht1) ht0.le (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  have e : (1 - t) + t * (v - k) = V - k := by linarith [htv]
  rw [e] at hc
  have h0 : (1 - V / (k + 1)) - t * (1 - v / (k + 1)) = 0 := by
    rw [show (1 - V / (k + 1)) - t * (1 - v / (k + 1))
        = (t * (v - (k + 1)) - (V - (k + 1))) / (k + 1) by field_simp; ring, htv, sub_self,
      zero_div]
  have lin : (1 - V / (k + 1)) * Wk k = t * ((1 - v / (k + 1)) * Wk k) := by
    linear_combination (Wk k) * h0
  have hX : 0 ≤ t * ((1 - v / (k + 1)) * Wk k - Real.log (v - k)) := by
    have : t * ((1 - v / (k + 1)) * Wk k - Real.log (v - k))
        = (1 - V / (k + 1)) * Wk k - Real.log (V - k) + (Real.log (V - k) - t * Real.log (v - k)) := by
      rw [lin]; ring
    rw [this, hfV]; linarith
  exact (mul_nonneg_iff_of_pos_left ht0).1 hX

lemma v0_gt (k : ℝ) (hk : 0 < k) :
    k + 1 < Real.exp (Wk k + k + 1) ∧ Real.exp (Wk k + k + 1) * (-Wk k) = k + 1 := by
  obtain ⟨hW1, hW2, _⟩ := W_spec k hk
  have hK := keyW k hk
  have h4 : Real.exp (Wk k + k + 1) * Real.exp (-(Wk k + k + 1)) = 1 := by
    rw [← Real.exp_add]; simp
  have hv0 : Real.exp (Wk k + k + 1) * (-Wk k) = k + 1 := by
    linear_combination (-Real.exp (Wk k + k + 1)) * hK + (k + 1) * h4
  refine ⟨?_, hv0⟩
  nlinarith [mul_pos (Real.exp_pos (Wk k + k + 1)) (by linarith : (0:ℝ) < 1 + Wk k)]

lemma f_v0 (k : ℝ) (hk : 0 < k) : f k (Real.exp (Wk k + k + 1)) < 0 := by
  obtain ⟨hW1, hW2, _⟩ := W_spec k hk
  obtain ⟨hv0a, hv0⟩ := v0_gt k hk
  set v0 := Real.exp (Wk k + k + 1) with hv0d
  have hk1 : (k + 1) ≠ 0 := by linarith
  have hvW : v0 * Wk k = -(k + 1) := by linarith
  unfold f
  have hb : 1 < v0 - k := by linarith
  have hbne : v0 - k ≠ 0 := by linarith
  have hq : Real.log (v0 / (v0 - k)) < v0 / (v0 - k) - 1 := by
    apply Real.log_lt_sub_one_of_pos (div_pos (by linarith) (by linarith))
    intro h
    rw [div_eq_one_iff_eq hbne] at h
    linarith
  have hsplit : Real.log v0 = Real.log (v0 - k) + Real.log (v0 / (v0 - k)) := by
    rw [← Real.log_mul hbne (div_pos (by linarith) (by linarith)).ne']
    congr 1; field_simp
  have hq2 : v0 / (v0 - k) - 1 = k / (v0 - k) := by field_simp; ring
  have hq3 : k / (v0 - k) < k := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hlog : Real.log v0 = Wk k + k + 1 := by rw [hv0d, Real.log_exp]
  have hlin : (1 - v0 / (k + 1)) * Wk k = Wk k + 1 := by
    have : (1 - v0 / (k + 1)) * Wk k = Wk k - (v0 * Wk k) / (k + 1) := by ring
    rw [this, hvW, neg_div, div_self hk1]; ring
  rw [hlin]
  linarith

lemma vf_spec (k : ℝ) (hk : 0 < k) :
    k + 1 < vf k ∧ f k (vf k) = 0 ∧ Real.exp (Wk k + k + 1) < vf k := by
  obtain ⟨hW1, hW2, _⟩ := W_spec k hk
  obtain ⟨hv0a, hv0⟩ := v0_gt k hk
  have hf0 := f_v0 k hk
  set v0 := Real.exp (Wk k + k + 1) with hv0d
  have hk1 : (k + 1) ≠ 0 := by linarith
  set δ := -Wk k / (k + 1) with hδd
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  set l := Real.log (δ / 2) with hl
  set V := v0 + k + 2 * (δ + |l| + 1) / δ with hVd
  have hpos2 : 0 < 2 * (δ + |l| + 1) / δ := div_pos (by positivity) hδ
  have hv0pos : 0 < v0 := Real.exp_pos _
  have hVk : δ / 2 * (V - k) = δ / 2 * v0 + (δ + |l| + 1) := by
    rw [hVd]; field_simp; ring
  have hVkpos : 0 < V - k := by linarith
  have hlogle : Real.log (V - k) ≤ δ / 2 * (V - k) - 1 - l := by
    have := Real.log_le_sub_one_of_pos (mul_pos (half_pos hδ) hVkpos)
    rw [Real.log_mul (half_pos hδ).ne' hVkpos.ne'] at this
    linarith
  have hfeq : f k V = δ * (V - (k + 1)) - Real.log (V - k) := by
    unfold f; rw [hδd]; field_simp; ring
  have habs := neg_abs_le l
  have hfV : 0 < f k V := by
    rw [hfeq]
    have : 0 < δ / 2 * v0 := mul_pos (half_pos hδ) hv0pos
    nlinarith
  have hle : v0 ≤ V := by linarith
  have hcont : ContinuousOn (fun v => f k v) (Set.Icc v0 V) := by
    unfold f
    apply ContinuousOn.sub (by fun_prop)
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    have := hx.1
    exact ne_of_gt (by linarith)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hle hcont ⟨hf0.le, hfV.le⟩
  have hfu' : f k u = 0 := hfu
  have hex : ∃ v : ℝ, k + 1 < v ∧ f k v = 0 := ⟨u, by linarith [hu.1], hfu'⟩
  have hvf : vf k = Classical.choose hex := by
    unfold vf; rw [dif_pos hex]
  obtain ⟨hA, hB⟩ := Classical.choose_spec hex
  rw [← hvf] at hA hB
  refine ⟨hA, hB, ?_⟩
  by_contra hc; push Not at hc
  have := f_nonneg k (vf k) v0 hk hA hB hc
  linarith

lemma pi3_sub_pi4 (v k : ℝ) (hk : 0 < k) : pi3 v k - pi4 v k = - f k v := by
  have hK := keyW k hk
  have hk1 : (k + 1) ≠ 0 := by linarith
  have hE : Real.exp (-(Wk k + k + 1)) = -Wk k / (k + 1) := by
    rw [eq_div_iff hk1]; exact hK
  unfold pi3 pi4 f
  rw [hE]; field_simp; ring

lemma pi3_le_pi2 (v k : ℝ) (hk : 0 < k) (hv : 0 < v) : pi3 v k ≤ pi2 v := by
  have hY := hys k hk
  have := prof_le v (Wk k + k + 1) hv
  unfold pi3 pi2
  nlinarith

lemma pi4_le_pi2 (v k : ℝ) (hk : 0 < k) (hb : 1 ≤ v - k) : pi4 v k ≤ pi2 v := by
  unfold pi4 pi2
  have hbpos : 0 < v - k := by linarith
  have hv : 0 < v := by linarith
  have hq := Real.log_le_sub_one_of_pos (div_pos hv hbpos)
  have hsplit : Real.log v = Real.log (v - k) + Real.log (v / (v - k)) := by
    rw [← Real.log_mul hbpos.ne' (div_pos hv hbpos).ne']
    congr 1; field_simp
  have hq2 : v / (v - k) - 1 = k / (v - k) := by field_simp; ring
  have hq3 : k / (v - k) ≤ k := by
    rw [div_le_iff₀ hbpos]; nlinarith
  linarith

lemma phi_pos (x : ℝ) (hx : 0 < x) : phi x = (1 - Real.exp (-x)) / x := by
  unfold phi; rw [if_neg hx.ne']

lemma phi_zero : phi 0 = 1 := by unfold phi; simp

lemma u1_eq (v k p x : ℝ) (hx : 0 < x) (h : u1 v k p x = 0) :
    (v - p - k) * (1 - Real.exp (-x)) = x := by
  unfold u1 at h; rw [phi_pos x hx] at h
  have h' : (v - p - k) * ((1 - Real.exp (-x)) / x) = 1 := by linarith
  rw [mul_div_assoc', div_eq_one_iff_eq hx.ne'] at h'
  exact h'

lemma u2_eq (v p x y : ℝ) (hy : 0 < y) (h : u2 v p x y = 0) :
    Real.exp (-x) * (v - p) * (1 - Real.exp (-y)) = y := by
  unfold u2 at h; rw [phi_pos y hy] at h
  have h' : Real.exp (-x) * (v - p) * ((1 - Real.exp (-y)) / y) = 1 := by linarith
  rw [mul_div_assoc', div_eq_one_iff_eq hy.ne'] at h'
  exact h'

lemma tanh_bd (y : ℝ) (hy : 0 ≤ y) : 2 * (1 - Real.exp (-y)) ≤ y * (1 + Real.exp (-y)) := by
  have hF0 : 0 < Real.exp (-y) := Real.exp_pos _
  have hF1 : Real.exp (-y) ≤ 1 := by
    have := Real.exp_le_exp.2 (by linarith : -y ≤ 0); rwa [Real.exp_zero] at this
  have hFe : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  generalize Real.exp (-y) = F at hF0 hF1 hFe ⊢
  have hpos : 0 < 1 + F := by linarith
  have hne : 1 + F ≠ 0 := hpos.ne'
  set z := (1 - F) / (1 + F) with hz
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hpos.le
  have hz1 : z < 1 := by rw [hz, div_lt_one hpos]; linarith
  have habs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := le_hasSum hs 0 (fun j _ => mul_nonneg (by positivity) (pow_nonneg hz0 _))
  norm_num at hle
  have e1 : 1 + z = 2 / (1 + F) := by rw [hz]; field_simp; ring
  have e2 : 1 - z = 2 * F / (1 + F) := by rw [hz]; field_simp; ring
  have e3 : 2 / (1 + F) = (2 * F / (1 + F)) * Real.exp y := by
    rw [div_mul_eq_mul_div, mul_assoc, hFe, mul_one]
  have hlogs : Real.log (1 + z) - Real.log (1 - z) = y := by
    rw [e1, e2, e3, Real.log_mul (div_pos (by linarith) hpos).ne' (Real.exp_pos y).ne',
      Real.log_exp]; ring
  rw [hlogs] at hle
  have h2 : 2 * (1 - F) / (1 + F) ≤ y := by rw [mul_div_assoc]; linarith
  exact (div_le_iff₀ hpos).1 h2

lemma typeD_alg (k c x y E F : ℝ) (hk : 0 < k)
    (hE0 : 0 < E) (hs0 : 0 < 1 - E) (hsx : 1 - E < x)
    (hr0 : 0 < 1 - F) (hry : 1 - F < y)
    (htanh : 2 * (1 - F) ≤ y * (1 + F)) (hI : 2 * E * x ≤ 1 - E ^ 2)
    (h1 : c * (1 - E) = x) (h2 : E * (c + k) * (1 - F) = y) :
    x + y ≤ (k + 1) * (1 - E * F) := by
  have hc1 : 1 < c := by
    by_contra hcc; push Not at hcc
    have := mul_le_mul_of_nonneg_right hcc hs0.le
    linarith
  have hm1 : 1 < E * (c + k) := by
    by_contra hmm; push Not at hmm
    have := mul_le_mul_of_nonneg_right hmm hr0.le
    linarith
  have hmF : 2 ≤ E * (c + k) * (1 + F) := by
    have : 2 * (1 - F) ≤ (E * (c + k) * (1 + F)) * (1 - F) := by
      rw [← h2] at htanh; linarith
    exact le_of_mul_le_mul_right this hr0
  have hrm : (1 - F) * (E * (c + k)) ≤ 2 * (E * (c + k) - 1) := by linarith
  have hI' : 0 ≤ 1 - E ^ 2 - 2 * E * (c * (1 - E)) := by rw [h1]; linarith
  have hid : E * (1 - E) * ((k + 1 - c) * (1 - E) * (E * (c + k)) - 2 * E * (c - 1) * (E * (c + k) - 1))
      = (1 - E) * (1 - E ^ 2 - 2 * E * (c * (1 - E)))
        + (E * (c + k) - 1) * ((1 - E ^ 2 - 2 * E * (c * (1 - E))) + (1 - E) ^ 3)
        + (E * (c + k) - 1) ^ 2 * (1 - E) ^ 2 := by ring
  have hR : 0 ≤ (1 - E) * (1 - E ^ 2 - 2 * E * (c * (1 - E)))
        + (E * (c + k) - 1) * ((1 - E ^ 2 - 2 * E * (c * (1 - E))) + (1 - E) ^ 3)
        + (E * (c + k) - 1) ^ 2 * (1 - E) ^ 2 := by
    have a1 := mul_nonneg hs0.le hI'
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ E * (c + k) - 1)
      (add_nonneg hI' (pow_nonneg hs0.le 3))
    have a3 := mul_nonneg (sq_nonneg (E * (c + k) - 1)) (sq_nonneg (1 - E))
    linarith
  have hP : 2 * E * (c - 1) * (E * (c + k) - 1) ≤ (k + 1 - c) * (1 - E) * (E * (c + k)) := by
    have hEs : 0 < E * (1 - E) := mul_pos hE0 hs0
    rw [← hid] at hR
    have := (mul_nonneg_iff_of_pos_left hEs).1 hR
    linarith
  have hkey : E * (c - 1) * (1 - F) ≤ (k + 1 - c) * (1 - E) := by
    have h3 : E * (c - 1) * ((1 - F) * (E * (c + k))) ≤ E * (c - 1) * (2 * (E * (c + k) - 1)) :=
      mul_le_mul_of_nonneg_left hrm (mul_nonneg hE0.le (by linarith))
    have h4 : (E * (c - 1) * (1 - F)) * (E * (c + k)) ≤ ((k + 1 - c) * (1 - E)) * (E * (c + k)) := by
      linarith
    exact le_of_mul_le_mul_right h4 (by linarith)
  rw [← h1, ← h2]
  linarith

lemma typeD (k c x y : ℝ) (hk : 0 < k) (hx : 0 < x) (hy : 0 < y)
    (h1 : c * (1 - Real.exp (-x)) = x)
    (h2 : Real.exp (-x) * (c + k) * (1 - Real.exp (-y)) = y) :
    x + y ≤ (k + 1) * (1 - Real.exp (-(x + y))) := by
  obtain ⟨hs0, hsx⟩ := one_sub_exp_lt x hx
  obtain ⟨hr0, hry⟩ := one_sub_exp_lt y hy
  have htanh := tanh_bd y hy.le
  have hI : 2 * Real.exp (-x) * x ≤ 1 - Real.exp (-x) ^ 2 := by
    have hs := (Real.self_le_sinh_iff).2 hx.le
    rw [Real.sinh_eq] at hs
    have hEx : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 2 * Real.exp (-x))
    nlinarith
  have hEF : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hEF]
  exact typeD_alg k c x y (Real.exp (-x)) (Real.exp (-y)) hk (Real.exp_pos _) hs0 hsx hr0 hry
    htanh hI h1 h2

/-- Every equilibrium profit is at most `pi2 v`, and, once `v ≥ e^{W+k+1}`, at most
`max (pi3 v k) (pi4 v k)`. -/
lemma bound_all (v k p x y : ℝ) (hk : 0 < k) (hv : 0 < v) (hp : 0 ≤ p)
    (he : IsEq v k p x y) :
    profit p x y ≤ pi2 v ∧
      (Real.exp (Wk k + k + 1) ≤ v → profit p x y ≤ max (pi3 v k) (pi4 v k)) := by
  obtain ⟨hW1, hW2, _⟩ := W_spec k hk
  have hY := hys k hk
  obtain ⟨hv0a, _⟩ := v0_gt k hk
  have hy0 : 0 < Wk k + k + 1 := by linarith
  have hsY : 0 < 1 - Real.exp (-(Wk k + k + 1)) := (one_sub_exp_lt _ hy0).1
  have hpi2 : 0 ≤ pi2 v := by
    unfold pi2; have := Real.log_le_sub_one_of_pos hv; linarith
  have hpi3_23 := pi3_le_pi2 v k hk hv
  obtain ⟨hx0, hy0', hx1, hx2, hy1, hy2⟩ := he
  rcases hx0.eq_or_lt with hx | hx <;> rcases hy0'.eq_or_lt with hy | hy
  · -- x = 0, y = 0
    subst hx; subst hy
    have : profit p 0 0 = 0 := by simp [profit]
    rw [this]
    refine ⟨hpi2, fun hv0 => le_max_of_le_left ?_⟩
    unfold pi3
    exact mul_nonneg (by linarith) hsY.le
  · -- x = 0, y > 0
    subst hx
    have hu2 := u2_eq v p 0 y hy (hy2 hy)
    have hu1 := hx1 rfl
    unfold u1 at hu1; rw [phi_zero] at hu1
    rw [neg_zero, Real.exp_zero, one_mul] at hu2
    have hpr : profit p 0 y = v * (1 - Real.exp (-y)) - y := by
      unfold profit; rw [zero_add]; linarith
    rw [hpr]
    refine ⟨prof_le v y hv, fun hv0 => le_max_of_le_left ?_⟩
    obtain ⟨hr0, _⟩ := one_sub_exp_lt y hy
    have hyle : y ≤ (k + 1) * (1 - Real.exp (-y)) := by
      have := mul_le_mul_of_nonneg_right (by linarith : v - p ≤ k + 1) hr0.le
      linarith
    have hyY := T_le k y hk hyle
    have ht := exp_tan (-y) (-(Wk k + k + 1))
    have hvE : 1 ≤ v * Real.exp (-(Wk k + k + 1)) := by
      have h4 : Real.exp (Wk k + k + 1) * Real.exp (-(Wk k + k + 1)) = 1 := by
        rw [← Real.exp_add]; simp
      have := mul_le_mul_of_nonneg_right hv0 (Real.exp_pos (-(Wk k + k + 1))).le
      linarith
    have hm := mul_le_mul_of_nonneg_left ht hv.le
    have hprod := mul_nonneg (sub_nonneg.2 hyY) (sub_nonneg.2 hvE)
    unfold pi3
    nlinarith
  · -- x > 0, y = 0
    subst hy
    have hu1 := u1_eq v k p x hx (hx2 hx)
    obtain ⟨hs0, hsx⟩ := one_sub_exp_lt x hx
    have hc1 : 1 < v - p - k := by
      by_contra hcc; push Not at hcc
      have := mul_le_mul_of_nonneg_right hcc hs0.le
      linarith
    have hb : 0 < v - k := by linarith
    have hpr : profit p x 0 = (v - k) * (1 - Real.exp (-x)) - x := by
      unfold profit; rw [add_zero]; linarith
    rw [hpr]
    have h4 := prof_le (v - k) x hb
    have h4' : (v - k) * (1 - Real.exp (-x)) - x ≤ pi4 v k := by unfold pi4; linarith
    refine ⟨le_trans h4' (pi4_le_pi2 v k hk (by linarith)), fun _ => le_max_of_le_right h4'⟩
  · -- x > 0, y > 0
    have hu1 := u1_eq v k p x hx (hx2 hx)
    have hu2 := u2_eq v p x y hy (hy2 hy)
    obtain ⟨hs0, hsx⟩ := one_sub_exp_lt x hx
    have hc1 : 1 ≤ v - p - k := by
      by_contra hcc; push Not at hcc
      have := mul_le_mul_of_nonneg_right hcc.le hs0.le
      linarith
    have hu2' : Real.exp (-x) * ((v - p - k) + k) * (1 - Real.exp (-y)) = y := by
      rw [show (v - p - k) + k = v - p by ring]; exact hu2
    have hT := T_le k (x + y) hk (typeD k (v - p - k) x y hk hx hy hu1 hu2')
    have hexp : Real.exp (-(Wk k + k + 1)) ≤ Real.exp (-(x + y)) :=
      Real.exp_le_exp.2 (by linarith)
    have hP3 : profit p x y ≤ pi3 v k := by
      unfold profit pi3
      have h5 : p * (1 - Real.exp (-(x + y))) ≤ p * (1 - Real.exp (-(Wk k + k + 1))) :=
        mul_le_mul_of_nonneg_left (by linarith) hp
      have h6 : p * (1 - Real.exp (-(Wk k + k + 1))) ≤ (v - k - 1) * (1 - Real.exp (-(Wk k + k + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) hsY.le
      linarith
    exact ⟨le_trans hP3 hpi3_23, fun _ => le_max_of_le_left hP3⟩

lemma zero_eq (v k p x y : ℝ) (hk : 0 < k) (hv : v ≤ 1) (hp : 0 ≤ p)
    (he : IsEq v k p x y) : x = 0 ∧ y = 0 := by
  obtain ⟨hx0, hy0, hx1, hx2, hy1, hy2⟩ := he
  have hx : x = 0 := by
    rcases hx0.eq_or_lt with h | h
    · exact h.symm
    · exfalso
      have hu1 := u1_eq v k p x h (hx2 h)
      obtain ⟨hs0, hsx⟩ := one_sub_exp_lt x h
      have := mul_pos (by linarith : (0:ℝ) < 1 - (v - p - k)) hs0
      nlinarith
  refine ⟨hx, ?_⟩
  subst hx
  rcases hy0.eq_or_lt with h | h
  · exact h.symm
  · exfalso
    have hu2 := u2_eq v p 0 y h (hy2 h)
    rw [neg_zero, Real.exp_zero, one_mul] at hu2
    obtain ⟨hs0, hsx⟩ := one_sub_exp_lt y h
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (v - p)) hs0.le
    nlinarith

lemma eq00 (v k : ℝ) (hk : 0 < k) (hv : v ≤ 1) : IsEq v k 0 0 0 := by
  refine ⟨le_refl _, le_refl _, fun _ => ?_, fun h => absurd h (lt_irrefl _), fun _ => ?_,
    fun h => absurd h (lt_irrefl _)⟩
  · unfold u1; rw [phi_zero]; linarith
  · unfold u2; rw [phi_zero, neg_zero, Real.exp_zero]; linarith

lemma greatest_zero (v k : ℝ) (hk : 0 < k) (hv : v ≤ 1) : IsGreatest (Profits v k) 0 := by
  refine ⟨⟨0, 0, 0, le_refl _, eq00 v k hk hv, by simp [profit]⟩, ?_⟩
  rintro z ⟨p, x, y, hp, he, rfl⟩
  obtain ⟨rfl, rfl⟩ := zero_eq v k p x y hk hv hp he
  simp [profit]

end AS4Aux

open AdvanceSales.Pricing in
theorem solution (v k : ℝ) (hk : 0 < k) :
    (v < 1 →
      (∀ p x y : ℝ, 0 ≤ p → IsEq v k p x y → x = 0 ∧ y = 0) ∧
      IsGreatest (Profits v k) 0) ∧
    (v = 1 →
      (∀ p x y : ℝ, 0 ≤ p → IsEq v k p x y → x = 0 ∧ y = Real.log v) ∧
      IsGreatest (Profits v k) (pi2 v)) ∧
    (1 < v → v ≤ Real.exp (Wk k + k + 1) →
      0 ≤ p2 v ∧ IsEq v k (p2 v) 0 (Real.log v) ∧
      profit (p2 v) 0 (Real.log v) = pi2 v ∧
      IsGreatest (Profits v k) (pi2 v)) ∧
    (Real.exp (Wk k + k + 1) < v → v ≤ vf k →
      0 ≤ p3 v k ∧ IsEq v k (p3 v k) 0 (Wk k + k + 1) ∧
      profit (p3 v k) 0 (Wk k + k + 1) = pi3 v k ∧
      IsGreatest (Profits v k) (pi3 v k)) ∧
    (vf k < v →
      0 ≤ p4 v k ∧ IsEq v k (p4 v k) (Real.log (v - k)) 0 ∧
      profit (p4 v k) (Real.log (v - k)) 0 = pi4 v k ∧
      IsGreatest (Profits v k) (pi4 v k)) := by
  obtain ⟨hW1, hW2, _⟩ := AS4Aux.W_spec k hk
  have hY := AS4Aux.hys k hk
  have hK := AS4Aux.keyW k hk
  obtain ⟨hv0a, hv0⟩ := AS4Aux.v0_gt k hk
  obtain ⟨hvfa, hvf0, hvfv0⟩ := AS4Aux.vf_spec k hk
  have hy0 : 0 < Wk k + k + 1 := by linarith
  refine ⟨fun hv => ⟨fun p x y hp he => AS4Aux.zero_eq v k p x y hk hv.le hp he,
      AS4Aux.greatest_zero v k hk hv.le⟩, ?_, ?_, ?_, ?_⟩
  · -- v = 1
    intro hv
    subst hv
    have h0 : pi2 1 = 0 := by unfold pi2; simp
    rw [Real.log_one, h0]
    exact ⟨fun p x y hp he => AS4Aux.zero_eq 1 k p x y hk le_rfl hp he, AS4Aux.greatest_zero 1 k hk le_rfl⟩
  · -- regime 2
    intro hv1 hvY
    have hv : 0 < v := by linarith
    have hL : 0 < Real.log v := Real.log_pos hv1
    have hLY : Real.log v ≤ Wk k + k + 1 := by
      rw [← Real.log_exp (Wk k + k + 1)]; exact Real.log_le_log hv hvY
    have hinv : Real.exp (-Real.log v) = v⁻¹ := by rw [Real.exp_neg, Real.exp_log hv]
    have hs : 0 < 1 - 1 / v := by
      rw [sub_pos, div_lt_one hv]; exact hv1
    have hvne : v ≠ 0 := hv.ne'
    have hsne : 1 - 1 / v ≠ 0 := hs.ne'
    have hv1a : v - 1 ≠ 0 := (by linarith : (0:ℝ) < v - 1).ne'
    have hv1b : -1 + v ≠ 0 := (by linarith : (0:ℝ) < -1 + v).ne'
    have hLv := Real.log_le_sub_one_of_pos hv
    have hpsi := AS4Aux.psi_nonneg k (Real.log v) hk hL.le hLY
    rw [hinv] at hpsi
    have hp2 : 0 ≤ p2 v := by
      unfold p2
      rw [sub_nonneg, div_le_iff₀ hs]
      have : v * (1 - 1 / v) = v - 1 := by field_simp
      rw [this]; exact hLv
    have heq : IsEq v k (p2 v) 0 (Real.log v) := by
      refine ⟨le_refl _, hL.le, fun _ => ?_, fun h => absurd h (lt_irrefl _),
        fun h => absurd h hL.ne', fun _ => ?_⟩
      · unfold u1 p2; rw [AS4Aux.phi_zero]
        have : Real.log v / (1 - 1 / v) ≤ k + 1 := by
          rw [div_le_iff₀ hs]
          have : (1 - 1 / v) = 1 - v⁻¹ := by rw [one_div]
          rw [this]; linarith
        linarith
      · unfold u2 p2; rw [AS4Aux.phi_pos _ hL, hinv, neg_zero, Real.exp_zero]
        field_simp
        ring
    have hpr : profit (p2 v) 0 (Real.log v) = pi2 v := by
      unfold profit p2 pi2
      rw [zero_add, hinv]
      field_simp
    refine ⟨hp2, heq, hpr, ⟨⟨p2 v, 0, Real.log v, hp2, heq, hpr.symm⟩, ?_⟩⟩
    rintro z ⟨p, x, y, hp, he, rfl⟩
    exact (AS4Aux.bound_all v k p x y hk hv hp he).1
  · -- regime 3
    intro hvY hvf
    have hv : 0 < v := by linarith
    have hp3 : 0 ≤ p3 v k := by unfold p3; linarith
    have heq : IsEq v k (p3 v k) 0 (Wk k + k + 1) := by
      refine ⟨le_refl _, hy0.le, fun _ => ?_, fun h => absurd h (lt_irrefl _),
        fun h => absurd h hy0.ne', fun _ => ?_⟩
      · unfold u1 p3; rw [AS4Aux.phi_zero]; linarith
      · unfold u2 p3; rw [AS4Aux.phi_pos _ hy0, neg_zero, Real.exp_zero]
        have e : v - (v - k - 1) = k + 1 := by ring
        rw [e, one_mul, mul_div_assoc', hY, div_self hy0.ne']; ring
    have hpr : profit (p3 v k) 0 (Wk k + k + 1) = pi3 v k := by
      unfold profit p3 pi3; rw [zero_add]
    refine ⟨hp3, heq, hpr, ⟨⟨p3 v k, 0, Wk k + k + 1, hp3, heq, hpr.symm⟩, ?_⟩⟩
    rintro z ⟨p, x, y, hp, he, rfl⟩
    have hb := (AS4Aux.bound_all v k p x y hk hv hp he).2 hvY.le
    have hf := AS4Aux.f_nonpos k (vf k) v hk hvfa hvf0 (by linarith) hvf
    have h34 := AS4Aux.pi3_sub_pi4 v k hk
    exact le_trans hb (max_le le_rfl (by linarith))
  · -- regime 4
    intro hvf
    have hv : 0 < v := by linarith
    have hf := AS4Aux.f_nonneg k (vf k) v hk hvfa hvf0 hvf.le
    have h34 := AS4Aux.pi3_sub_pi4 v k hk
    set b := v - k with hbd
    have hb1 : 1 < b := by linarith
    have hbpos : 0 < b := by linarith
    have hL : 0 < Real.log b := Real.log_pos hb1
    have hinv : Real.exp (-Real.log b) = b⁻¹ := by rw [Real.exp_neg, Real.exp_log hbpos]
    have hs : 0 < 1 - 1 / b := by rw [sub_pos, div_lt_one hbpos]; exact hb1
    have hbne : b ≠ 0 := hbpos.ne'
    have hsne : 1 - 1 / b ≠ 0 := hs.ne'
    have hb1a : b - 1 ≠ 0 := (by linarith : (0:ℝ) < b - 1).ne'
    have hb1b : -1 + b ≠ 0 := (by linarith : (0:ℝ) < -1 + b).ne'
    have hk1 : (k + 1) ≠ 0 := by linarith
    -- from f v ≥ 0 : log b * (k+1) ≤ (b - 1) * (-W)
    have hfL : Real.log b * (k + 1) ≤ (b - 1) * (-Wk k) := by
      unfold f at hf
      have e : (1 - v / (k + 1)) * Wk k = (b - 1) * (-Wk k) / (k + 1) := by
        rw [hbd]; field_simp; ring
      rw [e] at hf
      have : Real.log b ≤ (b - 1) * (-Wk k) / (k + 1) := by linarith
      rwa [le_div_iff₀ (by linarith)] at this
    have hlow := Real.one_sub_inv_le_log_of_pos hbpos
    have hbW : k + 1 ≤ b * (-Wk k) := by
      have h1 : (1 - b⁻¹) * (k + 1) ≤ (b - 1) * (-Wk k) :=
        le_trans (mul_le_mul_of_nonneg_right hlow (by linarith)) hfL
      have h2 : (1 - b⁻¹) * b = b - 1 := by field_simp
      have h3 : (b - 1) * (k + 1) ≤ (b - 1) * (b * (-Wk k)) := by
        have := mul_le_mul_of_nonneg_right h1 hbpos.le
        nlinarith
      exact le_of_mul_le_mul_left h3 (by linarith)
    have hstep : k * (k + 1) ≤ b * (k + 1 + Wk k) := by
      have h1 : (k + 1) * (k + 1 + Wk k) ≤ b * (-Wk k) * (k + 1 + Wk k) :=
        mul_le_mul_of_nonneg_right hbW (by linarith)
      have h2 : k * (k + 1) * (-Wk k) ≤ (k + 1) * (k + 1 + Wk k) := by
        have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k + 1) (by linarith : (0:ℝ) ≤ k + 1))
          (by linarith : (0:ℝ) ≤ 1 + Wk k)
        nlinarith
      have h3 : (k * (k + 1)) * (-Wk k) ≤ (b * (k + 1 + Wk k)) * (-Wk k) := by nlinarith
      exact le_of_mul_le_mul_right h3 (by linarith)
    have hbL : b * Real.log b ≤ (b - k) * (b - 1) := by
      have h1 : b * (Real.log b * (k + 1)) ≤ b * ((b - 1) * (-Wk k)) :=
        mul_le_mul_of_nonneg_left hfL hbpos.le
      have h2 : (b - 1) * (b * (-Wk k)) ≤ (b - 1) * ((b - k) * (k + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      have h3 : (b * Real.log b) * (k + 1) ≤ ((b - k) * (b - 1)) * (k + 1) := by nlinarith
      exact le_of_mul_le_mul_right h3 (by linarith)
    have hq : Real.log b / (1 - 1 / b) ≤ b - k := by
      rw [div_le_iff₀ hs]
      have : (b - k) * (1 - 1 / b) = (b - k) * (b - 1) / b := by field_simp
      rw [this, le_div_iff₀ hbpos]; linarith
    have hp4k : k ≤ p4 v k := by
      unfold p4; rw [← hbd]; linarith
    have hp4 : 0 ≤ p4 v k := by linarith
    have heq : IsEq v k (p4 v k) (Real.log b) 0 := by
      refine ⟨hL.le, le_refl _, fun h => absurd h hL.ne', fun _ => ?_, fun _ => ?_,
        fun h => absurd h (lt_irrefl _)⟩
      · unfold u1 p4; rw [AS4Aux.phi_pos _ hL, hinv, ← hbd]
        have e : v - (b - Real.log b / (1 - 1 / b)) - k = Real.log b / (1 - 1 / b) := by
          rw [hbd]; ring
        rw [e]
        field_simp
        ring
      · unfold u2; rw [AS4Aux.phi_zero, hinv]
        have e : v - p4 v k ≤ b := by linarith
        have : b⁻¹ * (v - p4 v k) ≤ 1 := by
          rw [inv_mul_le_iff₀ hbpos]; linarith
        linarith
    have hpr : profit (p4 v k) (Real.log b) 0 = pi4 v k := by
      unfold profit p4 pi4
      rw [add_zero, hinv, ← hbd]
      field_simp
    refine ⟨hp4, heq, hpr, ⟨⟨p4 v k, Real.log b, 0, hp4, heq, hpr.symm⟩, ?_⟩⟩
    rintro z ⟨p, x, y, hp, he, rfl⟩
    have hb := (AS4Aux.bound_all v k p x y hk hv hp he).2 (by linarith)
    exact le_trans hb (max_le (by linarith) le_rfl)
