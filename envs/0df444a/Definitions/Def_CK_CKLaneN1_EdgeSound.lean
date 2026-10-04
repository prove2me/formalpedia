-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeSound
-- name    : CK_CKLaneN1_EdgeSound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T19:26:21.334645+00:00
-- url     : https://prove2.me/theorems/9dcff3f5-0913-4151-95d6-45580ce4834a
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeSound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeSound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeSound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeSound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeSound.lean)

import Definitions.Def_CK_CKLaneN1_EdgeSound_part03

set_option autoImplicit false
namespace CKLaneN1.Edge
open GeneralCK CKLaneE.FP CKLaneN1.Capital Set
theorem eb1_le_half {B : B3} (h1 : 0 ≤ B.a0) (h2 : B.a0 < B.a1) (h3 : B.a1 ≤ 1)
    (_h4 : 0 ≤ B.b0) (h5 : B.b0 < B.b1) (h6 : B.b1 ≤ 1) : eb1 B ≤ 1 / 10000 := by
  simp only [eb1, bAt, mq, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem eM1_le {B : B3} (h1 : 0 ≤ B.a0) (h2 : B.a0 < B.a1) (_h3 : B.a1 ≤ 1)
    (_h4 : 0 ≤ B.b0) (h5 : B.b0 < B.b1) (h6 : B.b1 ≤ 1) : eM1 B ≤ 1 / 20000 := by
  simp only [eM1, MAt, mq, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-! ## Box soundness -/

set_option maxHeartbeats 4000000 in
/-- Soundness of one certified (non-corner) box: positivity of the cutoff-edge value at
`a = m(1-t)`, `b = m(1 + t(2z-1))`, `m = 1/20000`. -/
theorem edgeOK_sound {B : B3} {w : EWit} (hok : edgeOK B w = true) {t z : ℝ}
    (ht0 : (B.a0 : ℝ) ≤ t) (ht1 : t ≤ (B.a1 : ℝ)) (hz0 : (B.b0 : ℝ) ≤ z) (hz1 : z ≤ (B.b1 : ℝ))
    (htpos : 0 < t) (htl : t < 1) (hzpos : 0 < z) (hzl : z < 1) :
    0 < canonicalPureGap (1 / 20000 * (1 - t)) (1 / 10000 - 1 / 20000 * (1 - t))
      (H (1 / 20000 * (1 - t))) (H (1 / 20000 * (1 + t * (2 * z - 1)))) := by
  simp only [edgeOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hS, hL⟩, hT⟩, hV⟩, hQ⟩ := hok
  have hS' := hS
  simp only [eShapeOK, Bool.and_eq_true, decide_eq_true_eq] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩, hs6⟩, hs7⟩, hs8⟩ := hS'
  simp only [eLogsOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hla0, hla1⟩, hlb0⟩, hlb1⟩, hlM1⟩, hlh0⟩, hltail⟩, hllam⟩, hlrp⟩ := hL
  simp only [eThetaOK, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨hv1ok, hv1nn⟩, hv1br⟩, hv2ok⟩, hv2br⟩ := hT
  -- shape facts in ℝ
  have hs1R : (0 : ℝ) ≤ (B.a0 : ℝ) := by exact_mod_cast hs1
  have hs2R : (B.a0 : ℝ) < (B.a1 : ℝ) := by exact_mod_cast hs2
  have hs3R : (B.a1 : ℝ) ≤ 1 := by exact_mod_cast hs3
  have hs4R : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast hs4
  have hs5R : (B.b0 : ℝ) < (B.b1 : ℝ) := by exact_mod_cast hs5
  have hs6R : (B.b1 : ℝ) ≤ 1 := by exact_mod_cast hs6
  have hs7R : (0 : ℝ) < ((eb0 B : ℚ) : ℝ) := by exact_mod_cast hs7
  have hs8R : (0 : ℝ) < ((eM0 B : ℚ) : ℝ) := by exact_mod_cast hs8
  -- the chart
  set a : ℝ := 1 / 20000 * (1 - t) with hadef
  clear_value a
  set b : ℝ := 1 / 20000 * (1 + t * (2 * z - 1)) with hbdef
  clear_value b
  have ha : 0 < a := by rw [hadef]; nlinarith
  have htz : 0 < t * z := mul_pos htpos hzpos
  have htz' : 0 < t * (1 - z) := mul_pos htpos (by linarith)
  have hab : a < b := by rw [hadef, hbdef]; nlinarith
  have hbc : b < 1 / 10000 - a := by rw [hadef, hbdef]; nlinarith
  have hcS : 1 / 10000 - a < 1 / 2 := by rw [hadef]; nlinarith
  have hb2 : b < 1 / 2 := by linarith
  set y : ℝ := 1 / 10000 - 2 * a with hydef
  clear_value y
  have hyt : y = 1 / 10000 * t := by rw [hydef, hadef]; ring
  have hypos : 0 < y := by rw [hyt]; positivity
  have hd : b - a = z * y := by rw [hbdef, hadef, hyt]; ring
  -- box bounds
  have hA0 : ((ea0 B : ℚ) : ℝ) ≤ a := by
    simp only [ea0, mq]; push_cast; rw [hadef]; nlinarith
  have hA0' : (0 : ℝ) ≤ ((ea0 B : ℚ) : ℝ) := by
    simp only [ea0, mq]; push_cast; nlinarith
  have hA1 : a ≤ ((ea1 B : ℚ) : ℝ) := by
    simp only [ea1, mq]; push_cast; rw [hadef]; nlinarith
  have hA1' : ((ea1 B : ℚ) : ℝ) ≤ 1 / 20000 := by
    simp only [ea1, mq]; push_cast; nlinarith
  have hB0 : ((eb0 B : ℚ) : ℝ) ≤ b := by
    have := min4_le_bilin (B := B) bAt (1 / 20000) (-(1 / 20000)) (2 / 20000) bAt_cast ht0 ht1 hz0 hz1
    simp only [eb0]
    rw [hbdef]; linarith
  have hB1 : b ≤ ((eb1 B : ℚ) : ℝ) := by
    have := bilin_le_max4 (B := B) bAt (1 / 20000) (-(1 / 20000)) (2 / 20000) bAt_cast ht0 ht1 hz0 hz1
    simp only [eb1]
    rw [hbdef]; linarith
  have hB1' : ((eb1 B : ℚ) : ℝ) ≤ 1 / 10000 := by
    have := rle (eb1_le_half hs1 hs2 hs3 hs4 hs5 hs6); push_cast at this; linarith
  have hM0 : ((eM0 B : ℚ) : ℝ) ≤ (a + b) / 2 := by
    have := min4_le_bilin (B := B) MAt (1 / 20000) (-(1 / 20000)) (1 / 20000) MAt_cast ht0 ht1 hz0 hz1
    simp only [eM0]
    rw [hadef, hbdef]; linarith
  have hM1 : (a + b) / 2 ≤ ((eM1 B : ℚ) : ℝ) := by
    have := bilin_le_max4 (B := B) MAt (1 / 20000) (-(1 / 20000)) (1 / 20000) MAt_cast ht0 ht1 hz0 hz1
    simp only [eM1]
    rw [hadef, hbdef]; linarith
  have hM1' : ((eM1 B : ℚ) : ℝ) ≤ 1 / 20000 := by
    have := rle (eM1_le hs1 hs2 hs3 hs4 hs5 hs6); push_cast at this; linarith
  have hY0 : ((ey0 B : ℚ) : ℝ) ≤ y := by
    simp only [ey0, Sq]; push_cast; rw [hyt]; nlinarith
  have hY1 : y ≤ ((ey1 B : ℚ) : ℝ) := by
    simp only [ey1, Sq]; push_cast; rw [hyt]; nlinarith
  have hC1 : 1 / 10000 - a ≤ ((ec1 B : ℚ) : ℝ) := by
    simp only [ec1, mq]; push_cast; rw [hadef]; nlinarith
  have hrho : (b - a) / (a + b) ≤ ((erho1 B : ℚ) : ℝ) := by
    have hd1ne : (1 - t + t * z) ≠ 0 := by nlinarith
    have habne : a + b ≠ 0 := by linarith
    have e : (b - a) / (a + b) = t * z / (1 - t + t * z) := by
      rw [div_eq_div_iff habne hd1ne, hbdef, hadef]; ring
    rw [e]
    simp only [erho1]
    push_cast
    have hd1 : 0 < 1 - t + t * z := by nlinarith
    have hz1pos : (0 : ℝ) < B.b1 := by linarith
    have hd2 : (0 : ℝ) < 1 - B.a1 + B.b1 * B.a1 := by nlinarith
    rw [div_le_div_iff₀ hd1 hd2]
    have h1 : t * z * (1 - (B.a1 : ℝ)) ≤ t * B.b1 * (1 - B.a1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz1 htpos.le) (by linarith)
    have h2 : t * (1 - (B.a1 : ℝ)) ≤ B.a1 * (1 - t) := by nlinarith
    have h3 : (B.b1 : ℝ) * (t * (1 - B.a1)) ≤ B.b1 * (B.a1 * (1 - t)) :=
      mul_le_mul_of_nonneg_left h2 hz1pos.le
    nlinarith
  have hrhop : (b - a) / (2 * (1 - (a + b) / 2)) ≤ ((erhop1 B : ℚ) : ℝ) := by
    simp only [erhop1, mq]
    push_cast
    have hden : 0 < 1 - ((eM1 B : ℚ) : ℝ) := by linarith
    rw [div_le_div_iff₀ (by linarith) hden, hd, hyt]
    have hz1pos : (0 : ℝ) ≤ B.b1 := by linarith
    have h1 : z * t ≤ (B.b1 : ℝ) * B.a1 := mul_le_mul hz1 ht1 htpos.le hz1pos
    nlinarith
  have hrhop2 : ((erhop1 B : ℚ) : ℝ) ≤ 1 / 2 := by
    have := rle hlrp; push_cast at this ⊢; linarith
  -- entropies
  have hHa0 : 0 < H a := H_pos ha (by linarith)
  have hHb0 : 0 < H b := H_pos (by linarith) (by linarith)
  have hef : H a ≤ H b := H_mono ha.le hab.le hb2.le
  have hE0 : ((ee0 B : ℚ) : ℝ) ≤ H a := by
    simp only [ee0]
    split_ifs with h0
    · push_cast; exact hHa0.le
    · have hp : ptOk (ea0 B) = true := by
        rcases hla0 with h | h
        · exact absurd h h0
        · exact h
      exact (H_bounds hp).1.trans (H_mono hA0' hA0 (by linarith))
  have hE0' : (0 : ℝ) ≤ ((ee0 B : ℚ) : ℝ) := by
    simp only [ee0]
    split_ifs with h0
    · push_cast; exact le_refl _
    · have hp : ptOk (ea0 B) = true := by
        rcases hla0 with h | h
        · exact absurd h h0
        · exact h
      simp only [Hlo]
      split_ifs with hh
      · have := rle hh
        have hL := log_two_mem
        push_cast at this ⊢
        exact div_nonneg this (by linarith [LqLo_pos])
      · push_cast; exact le_refl _
  have hE1 : H a ≤ ((ee1 B : ℚ) : ℝ) := (H_mono ha.le hA1 (by linarith)).trans (H_bounds hla1).2
  have hF0 : ((ef0 B : ℚ) : ℝ) ≤ H b :=
    (H_bounds hlb0).1.trans (H_mono hs7R.le hB0 hb2.le)
  have hF1 : H b ≤ ((ef1 B : ℚ) : ℝ) :=
    (H_mono (by linarith) hB1 (by linarith)).trans (H_bounds hlb1).2
  set e : ℝ := H a with hedef
  clear_value e
  set f : ℝ := H b with hfdef
  clear_value f
  set h : ℝ := (e + f) / 2 with hhdef
  clear_value h
  have hH0 : ((eh0 B : ℚ) : ℝ) ≤ h := by
    simp only [eh0]; push_cast; rw [hhdef]; linarith
  have hH1 : h ≤ ((eh1 B : ℚ) : ℝ) := by
    simp only [eh1]; push_cast; rw [hhdef]; linarith
  have hH0p : (0 : ℝ) < ((eh0 B : ℚ) : ℝ) := rpos hlh0
  have hhpos : 0 < h := by linarith
  -- Theta at Xbar
  have hXbar : ((eXbar B : ℚ) : ℝ) = ((ey1 B : ℚ) : ℝ) / (2 * ((eh0 B : ℚ) : ℝ)) := by
    simp only [eXbar]; push_cast; ring
  have hY1p : (0 : ℝ) < ((ey1 B : ℚ) : ℝ) := hypos.trans_le hY1
  have hXbarp : (0 : ℝ) < ((eXbar B : ℚ) : ℝ) := by rw [hXbar]; positivity
  have hX : y / (2 * h) ≤ ((eXbar B : ℚ) : ℝ) := by
    rw [hXbar, div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul hY1 (by linarith only [hH0]) (by positivity) hY1p.le
  have hκ : ((slopeLo w.v1 : ℚ) : ℝ) ≤ e8Theta ((eXbar B : ℚ) : ℝ) := by
    apply theta_ge hXbarp hv1ok
    have := rle hv1br; push_cast at this ⊢; linarith
  have hκ0 : (0 : ℝ) ≤ ((slopeLo w.v1 : ℚ) : ℝ) := rnn hv1nn
  -- main pointwise bound
  have hmain := edge_main_lb (S := 1 / 10000) (X := ((eXbar B : ℚ) : ℝ)) ha hab hbc hcS
    (by rw [← hydef, ← hedef, ← hfdef, ← hhdef]; exact hX)
  rw [← hydef, ← hedef, ← hfdef, ← hhdef] at hmain
  obtain ⟨hqa, hqM, -, -⟩ := q_facts ha hab.le hb2
  rw [← hedef, ← hfdef, ← hhdef] at hqa hqM
  set q : ℝ := entropyInverse h with hqdef
  clear_value q
  have hq2 : q < 1 / 2 := by linarith
  -- T1
  have hT1 := T1_bound (y := y) (d := b - a) (sub_pos.mpr hab).le (by linarith) hhpos hH1
    hXbarp hκ hκ0
  -- T2
  have hT2 := T2_sound hV ha hab hb2 hypos hd hzpos.le hM1 hA1 (by linarith) hB0 (rpos hs7) hlb0 hY1
  -- T3
  have hXq : 0 < (1 - 2 * q) / (2 * h) := by
    have : 0 < 1 - 2 * q := by linarith
    positivity
  have hXhat : ((eXhat B : ℚ) : ℝ) = 1 / (2 * ((eh0 B : ℚ) : ℝ)) := by
    simp only [eXhat]; push_cast; ring
  have hXqle : (1 - 2 * q) / (2 * h) ≤ ((eXhat B : ℚ) : ℝ) := by
    rw [hXhat, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq0 : 0 ≤ q := by linarith only [hqa, ha]
    exact mul_le_mul (by linarith only [hq0]) (by linarith only [hH0]) (by positivity)
      (by norm_num)
  have hΘ1 : e8Theta ((1 - 2 * q) / (2 * h)) ≤ ((slopeHi w.v2 : ℚ) : ℝ) := by
    refine (theta_mono hXq hXqle).trans ?_
    apply theta_le (by rw [hXhat]; positivity) hv2ok
    have := rle hv2br; push_cast at this ⊢; linarith
  have hΘ0 : 0 ≤ e8Theta ((1 - 2 * q) / (2 * h)) := (e8Theta_pos hXq).le
  have hJMp : (0 : ℝ) < ((eJM1 B : ℚ) : ℝ) := by
    simp only [eJM1]; push_cast
    exact div_pos (rpos hllam) (by linarith [log_two_mem.2, Real.log_pos (by norm_num : (1:ℝ) < 2)])
  have hJM : ((eJM1 B : ℚ) : ℝ) ≤ J ((a + b) / 2) := by
    simp only [eJM1]
    have h1 := J_ge hlM1 (le_of_lt hllam)
    have h2 := J_anti (by linarith) hM1 (by linarith)
    push_cast at h1 ⊢
    linarith
  have hT3 := T3_sound hV ha hab hb2 hypos hd hΘ0 hΘ1 hM0 (rpos hs8) hM1 (by linarith) hJM hJMp
    hrho hrhop hrhop2 hY0
  rw [← hedef, ← hfdef, ← hhdef, ← hqdef] at hT3
  -- T4
  set c : ℝ := 1 / 10000 - a with hcdef
  clear_value c
  have hcb : c - b = y * (1 - z) := by rw [hcdef, hbdef, hyt, hadef]; ring
  have hcq : c - q ≤ y := by rw [hcdef, hydef]; linarith
  have hc1' : 0 < 1 - 2 * ((ec1 B : ℚ) : ℝ) := by
    have := rle hltail; push_cast at this
    have hf1p : 0 < ((ef1 B : ℚ) : ℝ) := hHb0.trans_le hF1
    linarith
  have hqc : q ≤ c := by rw [hcdef]; linarith
  have hXc : 0 < (1 - 2 * c) / (2 * f) := by
    have : 0 < 1 - 2 * c := by linarith
    positivity
  have hXc128 : 128 ≤ (1 - 2 * c) / (2 * f) := by
    have ht := rle hltail; push_cast at ht
    rw [le_div_iff₀ (by positivity)]
    linarith only [ht, hF1, hC1]
  have hXcq : (1 - 2 * c) / (2 * f) ≤ (1 - 2 * q) / (2 * h) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 < 1 - 2 * c := by linarith
    have hhf : h ≤ f := by rw [hhdef]; linarith only [hef]
    exact mul_le_mul (by linarith only [hqc]) (by linarith only [hhf]) (by positivity)
      (by linarith only [hq2])
  have hΘtail := theta_increment_tail hXc128 hXcq
  have hΘmono := theta_mono hXc hXcq
  have hfe : f - e ≤ J a * (b - a) := by
    rw [hedef, hfdef]; exact H_sub_le_J ha hab.le (by linarith)
  have hJa : ∀ _ : 0 < ((ea0 B : ℚ) : ℝ), ptOk (ea0 B) = true →
      J a ≤ ((lamHi (ea0 B) : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
    intro h0 hp
    exact (J_anti h0 hA0 (by linarith)).trans (J_le hp (by linarith))
  have hJa0 : 0 ≤ J a := (J_pos ha (by linarith)).le
  have hT4 := T4_sound hV hab hypos hd hzl.le hcb hcq hC1 hc1' hqc hE0 hE0' hef hF1 hhdef hH0 hH0p
    hfe hJa hJa0 hY0 hΘtail
  -- polynomial positivity
  have hP := qposOK_sound hQ hz0 hz1
  have hy2 : 0 < y ^ 2 := by positivity
  have hPy := mul_pos hy2 hP
  have eP : y ^ 2 * (((eP0 B w : ℚ) : ℝ) + ((eP1 B w : ℚ) : ℝ) * z + ((eP2 B w : ℚ) : ℝ) * z ^ 2) =
      ((slopeLo w.v1 : ℚ) : ℝ) / ((eXbar B : ℚ) : ℝ) / (4 * ((eh1 B : ℚ) : ℝ)) *
          (y ^ 2 - (b - a) ^ 2) +
        y ^ 2 * (((eT2 B w).1 : ℝ) * z + ((eT2 B w).2 : ℝ) * z ^ 2) -
        y ^ 2 * (((eT3 B w).1 : ℝ) + ((eT3 B w).2 : ℝ) * z ^ 2) -
        y ^ 2 * (((eT4 B w).1 : ℝ) + ((eT4 B w).2.1 : ℝ) * z + ((eT4 B w).2.2 : ℝ) * z ^ 2) := by
    rw [hd]
    simp only [eP0, eP1, eP2, eA]
    push_cast
    ring
  have hre : (2 * q - 1 / 10000) * e8Theta ((1 - 2 * q) / (2 * h)) +
      (c - b) * e8Theta ((1 - 2 * c) / (2 * f)) =
      -((a + b - 2 * q) * e8Theta ((1 - 2 * q) / (2 * h))) -
        (c - b) * (e8Theta ((1 - 2 * q) / (2 * h)) - e8Theta ((1 - 2 * c) / (2 * f))) := by
    rw [hcdef]; ring
  linarith only [hmain, hT1, hT2, hT3, hT4, hre, eP, hPy]

end CKLaneN1.Edge


