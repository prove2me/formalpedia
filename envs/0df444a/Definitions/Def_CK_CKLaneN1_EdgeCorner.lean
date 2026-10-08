-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeCorner
-- name    : CK_CKLaneN1_EdgeCorner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T04:24:47.133952+00:00
-- url     : https://prove2.me/theorems/6a8da1e9-743e-49b4-8daa-82864a63e3df
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeCorner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeCorner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeCorner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeCorner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeCorner.lean)

import Definitions.Def_CK_CKLaneN1_EdgeSound

-- ===== source module CKLaneN1.EdgeCorner =====
section

set_option autoImplicit false

/-!
# Lane N1: the leftEdge corner `t ≥ 1023/1024`, `z ≤ 1/2048` (both means `≤ β = 1/10240000`)

Here `F y h - F d h ≥ (y - d) J v̄` (chord of the convex profile and a contact bracket), the
Jensen penalty is `≤ b (Θ 128 + (81/50) log (1/(128 b))) ≤ β (Θ 128 + (81/50)(1 + log 80000))`
and the outer penalty is `≤ S (81/50) (2S/(1-2S) + log 2)`.  All constants are kernel-checked.
-/

namespace CKLaneN1.Edge

open GeneralCK CKLaneE.FP CKLaneN1.Capital Set

def betaQ : ℚ := 1 / 10240000
def cornerV : ℚ := dy 2729560443809023 60
def cornerW : ℚ := dy 341940023070001 60

/-- Kernel-checked corner constants. -/
theorem corner_facts :
    ptOk betaQ = true ∧ ptOk cornerV = true ∧ 0 ≤ lamLo cornerV ∧ cornerV ≤ 1 / 2 ∧
    Hhi betaQ * (1 - 2 * cornerV) ≤ (1 / 10000) * (1023 / 1024) * Hlo cornerV ∧
    slopeHiOk cornerW = true ∧ 2 * 128 * Hhi cornerW ≤ 1 - 2 * cornerW ∧
    ptOk (1 / 80000) = true ∧ 256 * Hhi betaQ ≤ 1 - 2 * (1 / 10000) ∧
    betaQ * slopeHi cornerW + 81 / 50 * betaQ * (1 + -lLo (1 / 80000)) +
        1 / 10000 * (81 / 50) * (2 * (1 / 10000) / (1 - 2 * (1 / 10000)) + LqHi) <
      (1 / 10000 - 2 * betaQ) * (lamLo cornerV / LqHi) := by
  decide +kernel

/-- `H b ≥ b` on `(0, 1/2]`. -/
theorem H_ge_self {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 2) : b ≤ H b := by
  unfold H
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hL0]
  have h1 : Real.log 2 ≤ -Real.log b := by
    rw [← Real.log_inv]
    exact Real.log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) hb0]; linarith)
  have h2 : 0 ≤ Real.negMulLog (1 - b) := Real.negMulLog_nonneg (by linarith) (by linarith)
  have h3 : b * Real.log 2 ≤ b * (-Real.log b) := mul_le_mul_of_nonneg_left h1 hb0.le
  have e : Real.negMulLog b = b * (-Real.log b) := by simp only [Real.negMulLog]; ring
  linarith

/-- Chord bound on the ratio term. -/
theorem corner_T1 {y d h κ : ℝ} (hy : 0 < y) (hd : 0 < d) (hdy : d ≤ y) (hh : 0 < h)
    (hκ : κ ≤ J (radialContact y h)) :
    (y - d) * κ ≤ F y h - F d h := by
  have hconv := convexOn_F_radius hh
  have h1 := hconv.2 (show (0 : ℝ) ∈ Ici 0 by simp) (show y ∈ Ici 0 from hy.le)
    (show 0 ≤ 1 - d / y by rw [sub_nonneg, div_le_one hy]; exact hdy)
    (show 0 ≤ d / y from div_nonneg hd.le hy.le)
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at h1
  have e1 : d / y * y = d := by field_simp
  rw [e1, show F 0 h = 0 by simp [F], mul_zero, zero_add] at h1
  have hFy : F y h = y * J (radialContact y h) := by simp only [F, hy.ne', if_false]
  have h2 : (y - d) * κ ≤ (y - d) * J (radialContact y h) :=
    mul_le_mul_of_nonneg_left hκ (by linarith)
  have h3 : F y h - d / y * F y h = (y - d) * J (radialContact y h) := by
    rw [hFy]; field_simp
  linarith

/-- Jensen penalty in the corner. -/
theorem corner_T3 {g b β Θq X sH L : ℝ} (_hg0 : 0 ≤ g) (hgb : g ≤ b) (hb0 : 0 < b)
    (hbβ : b ≤ β) (hX : X ≤ 1 / b) (hX128 : 128 ≤ X) (hΘq0 : 0 ≤ Θq)
    (hΘq : Θq - e8Theta 128 ≤ 81 / 50 * Real.log (X / 128)) (hΘ128 : e8Theta 128 ≤ sH)
    (hL : Real.log (1 / (128 * β)) ≤ L) (hβ128 : 128 * β ≤ 1) :
    g * Θq ≤ β * sH + 81 / 50 * β * (1 + L) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hb0 hbβ
  have hlogq : Real.log (X / 128) ≤ Real.log (1 / (128 * b)) := by
    apply Real.log_le_log (by positivity)
    rw [show 1 / (128 * b) = (1 / b) / 128 by field_simp]
    exact div_le_div_of_nonneg_right hX (by norm_num)
  have hsplit : Real.log (1 / (128 * b)) = Real.log (β / b) + Real.log (1 / (128 * β)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlb : b * Real.log (1 / (128 * b)) ≤ β * (1 + Real.log (1 / (128 * β))) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < β / b by positivity)
    have h2 : 0 ≤ Real.log (1 / (128 * β)) := by
      apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : b * Real.log (β / b) ≤ β - b := by
      have := mul_le_mul_of_nonneg_left h1 hb0.le
      have e : b * (β / b - 1) = β - b := by field_simp
      linarith
    have h4 : b * Real.log (1 / (128 * β)) ≤ β * Real.log (1 / (128 * β)) :=
      mul_le_mul_of_nonneg_right hbβ h2
    rw [hsplit, mul_add]
    linarith
  have hsH : 0 ≤ sH := (e8Theta_pos (by norm_num : (0:ℝ) < 128)).le.trans hΘ128
  have h1 : g * Θq ≤ b * Θq := mul_le_mul_of_nonneg_right hgb hΘq0
  have h2 : Θq ≤ sH + 81 / 50 * Real.log (1 / (128 * b)) := by linarith
  have h3 : b * Θq ≤ b * sH + 81 / 50 * (b * Real.log (1 / (128 * b))) := by
    have := mul_le_mul_of_nonneg_left h2 hb0.le
    linarith
  have h4 : b * sH ≤ β * sH := mul_le_mul_of_nonneg_right hbβ hsH
  have h5 : β * (1 + Real.log (1 / (128 * β))) ≤ β * (1 + L) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ0.le
  linarith

/-- Outer penalty in the corner. -/
theorem corner_T4 {cb Θd lq lf S Lh : ℝ} (hcb0 : 0 ≤ cb) (hcbS : cb ≤ S)
    (hΘ : Θd ≤ 81 / 50 * (lq + lf)) (hlq : lq ≤ 2 * S / (1 - 2 * S)) (hlf : lf ≤ Lh)
    (hsum : 0 ≤ 2 * S / (1 - 2 * S) + Lh) :
    cb * Θd ≤ S * (81 / 50) * (2 * S / (1 - 2 * S) + Lh) := by
  have h1 : Θd ≤ 81 / 50 * (2 * S / (1 - 2 * S) + Lh) := by linarith
  have h2 : cb * Θd ≤ cb * (81 / 50 * (2 * S / (1 - 2 * S) + Lh)) :=
    mul_le_mul_of_nonneg_left h1 hcb0
  have h3 : cb * (81 / 50 * (2 * S / (1 - 2 * S) + Lh)) ≤
      S * (81 / 50 * (2 * S / (1 - 2 * S) + Lh)) :=
    mul_le_mul_of_nonneg_right hcbS (by positivity)
  linarith

set_option maxHeartbeats 2000000 in
/-- Positivity of the cutoff-edge value on the corner box. -/
theorem corner_pos {t z : ℝ} (ht : (1023 / 1024 : ℝ) ≤ t) (htl : t < 1) (hz : 0 < z)
    (hzc : z ≤ 1 / 2048) :
    0 < canonicalPureGap (1 / 20000 * (1 - t)) (1 / 10000 - 1 / 20000 * (1 - t))
      (H (1 / 20000 * (1 - t))) (H (1 / 20000 * (1 + t * (2 * z - 1)))) := by
  obtain ⟨hpb, hpv, hlv, hv2, hbr, hwok, hwbr, hp8, htail, hfin⟩ := corner_facts
  have hL := log_two_mem
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ : ((betaQ : ℚ) : ℝ) = 1 / 10240000 := by norm_num [betaQ]
  have hv2R : ((cornerV : ℚ) : ℝ) ≤ 1 / 2 := by
    have := rle hv2; push_cast at this; linarith
  have hv0R : (0 : ℝ) < ((cornerV : ℚ) : ℝ) := by exact_mod_cast (ptOk_pos hpv).1
  have htpos : 0 < t := by linarith
  set a : ℝ := 1 / 20000 * (1 - t) with hadef
  clear_value a
  set b : ℝ := 1 / 20000 * (1 + t * (2 * z - 1)) with hbdef
  clear_value b
  have ha : 0 < a := by rw [hadef]; nlinarith
  have hab : a < b := by rw [hadef, hbdef]; nlinarith [mul_pos htpos hz]
  have hbc : b < 1 / 10000 - a := by
    rw [hadef, hbdef]; nlinarith [mul_pos htpos (by linarith : (0:ℝ) < 1 - z)]
  have hcS : 1 / 10000 - a < 1 / 2 := by rw [hadef]; nlinarith
  have hbβ : b ≤ 1 / 10240000 := by rw [hbdef]; nlinarith
  have hb2 : b < 1 / 2 := by linarith
  set y : ℝ := 1 / 10000 - 2 * a with hydef
  clear_value y
  have hyt : y = 1 / 10000 * t := by rw [hydef, hadef]; ring
  have hy0 : 1 / 10000 * (1023 / 1024) ≤ y := by rw [hyt]; linarith
  have hypos : 0 < y := by linarith
  -- entropies (facts before naming)
  have he0 : 0 < H a := H_pos ha (by linarith)
  have hf0 : 0 < H b := H_pos (by linarith) (by linarith)
  have hef : H a ≤ H b := H_mono ha.le hab.le hb2.le
  have hfβ : H b ≤ ((Hhi betaQ : ℚ) : ℝ) := by
    have h1 := H_mono (by linarith) hbβ (by norm_num)
    have h2 := (H_bounds hpb).2
    rw [hβ] at h2
    linarith
  have hHb : b ≤ H b := H_ge_self (by linarith) hb2.le
  rw [cpg_edge_eq ha hab hbc hcS.le]
  obtain ⟨hqa, hqM, -, -⟩ := q_facts ha hab.le hb2
  set e : ℝ := H a with hedef
  clear_value e
  set f : ℝ := H b with hfdef
  clear_value f
  set h : ℝ := (e + f) / 2 with hhdef
  clear_value h
  set q : ℝ := entropyInverse h with hqdef
  clear_value q
  rw [← hydef]
  set c : ℝ := 1 / 10000 - a with hcdef
  clear_value c
  have hhpos : 0 < h := by rw [hhdef]; linarith
  have hhβ : h ≤ ((Hhi betaQ : ℚ) : ℝ) := by rw [hhdef]; linarith
  have hhf : h ≤ f := by rw [hhdef]; linarith
  have hq2 : q < 1 / 2 := by linarith
  -- T1: chord + contact bracket
  have hcontact : radialContact y h ≤ ((cornerV : ℚ) : ℝ) := by
    apply (radialContact_le_iff hypos hhpos hv0R.le hv2R).2
    have hbrR := rle hbr
    push_cast at hbrR
    have hHv := (H_bounds hpv).1
    have h1 : h * (1 - 2 * ((cornerV : ℚ) : ℝ)) ≤
        ((Hhi betaQ : ℚ) : ℝ) * (1 - 2 * ((cornerV : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hhβ (by linarith)
    have hHv0 : 0 ≤ ((Hlo cornerV : ℚ) : ℝ) := by
      simp only [Hlo]; split_ifs with hh
      · have := rle hh; push_cast at this ⊢
        exact div_nonneg this (by linarith [LqLo_pos, hL.1])
      · push_cast; exact le_refl _
    have h2 : 1 / 10000 * (1023 / 1024) * ((Hlo cornerV : ℚ) : ℝ) ≤ y * H ((cornerV : ℚ) : ℝ) :=
      mul_le_mul hy0 hHv hHv0 hypos.le
    linarith
  have hJv : ((lamLo cornerV : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ J (radialContact y h) :=
    (J_ge hpv hlv).trans (J_anti (radialContact_pos hypos hhpos) hcontact (by linarith))
  have hJv0 : 0 ≤ ((lamLo cornerV : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) :=
    div_nonneg (rnn hlv) (by linarith [hL.2])
  have hd0 : 0 < b - a := sub_pos.mpr hab
  have hdy : b - a ≤ y := by rw [hydef]; linarith
  have hT1 := corner_T1 hypos hd0 hdy hhpos hJv
  have hyd : 1 / 10000 - 2 * (1 / 10240000 : ℝ) ≤ y - (b - a) := by
    rw [hydef]; linarith
  have hT1' : (1 / 10000 - 2 * (1 / 10240000 : ℝ)) *
      (((lamLo cornerV : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) ≤ F y h - F (b - a) h :=
    le_trans (mul_le_mul_of_nonneg_right hyd hJv0) hT1
  -- interior cost is nonnegative
  have hj : 0 ≤ interiorCost a b := by
    have := interiorCost_ge ha hab (by linarith)
    exact le_trans (div_nonneg (sq_nonneg _) (mul_pos (by linarith) hL0).le) this
  -- outer tangents
  have h2t := F_tangent (h := h) hhpos (x0 := 1 - 2 * q) (x := 1 - 1 / 10000) (by linarith)
    (by norm_num)
  have h3t := F_tangent (h := f) hf0 (x0 := 1 - 2 * c) (x := 1 - 2 * b)
    (by rw [hcdef]; linarith) (by linarith)
  -- Theta at X_q and X_c
  have ht2 : 256 * ((Hhi betaQ : ℚ) : ℝ) ≤ 1 - 2 * (1 / 10000) := by
    have := rle htail; push_cast at this; linarith
  have hXq : 128 ≤ (1 - 2 * q) / (2 * h) := by
    rw [le_div_iff₀ (by linarith)]
    linarith only [ht2, hhβ, hqM, hab, hbβ]
  have hc1 : c ≤ 1 / 10000 := by rw [hcdef]; linarith
  have hXc : 128 ≤ (1 - 2 * c) / (2 * f) := by
    rw [le_div_iff₀ (by linarith)]
    linarith only [ht2, hfβ, hc1]
  have hqc : q ≤ c := by rw [hcdef]; linarith
  have hXcq : (1 - 2 * c) / (2 * f) ≤ (1 - 2 * q) / (2 * h) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    exact mul_le_mul (by linarith only [hqc]) (by linarith only [hhf]) (by linarith)
      (by linarith only [hq2])
  have hΘ128 : e8Theta 128 ≤ ((slopeHi cornerW : ℚ) : ℝ) := by
    apply theta_le (by norm_num) hwok
    have := rle hwbr; push_cast at this ⊢; linarith
  have hΘq := theta_increment_tail (le_refl (128 : ℝ)) hXq
  have hΘqc := theta_increment_tail hXc hXcq
  have hΘqc0 := theta_mono (by linarith) hXcq
  -- Jensen penalty
  have hXqb : (1 - 2 * q) / (2 * h) ≤ 1 / b := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 : b ≤ 2 * h := by rw [hhdef]; linarith
    have h2 : 0 ≤ q := by linarith
    nlinarith only [h1, h2, hq2, hab, ha]
  have hL80 : Real.log (1 / (128 * (1 / 10240000 : ℝ))) ≤ ((-lLo (1 / 80000) : ℚ) : ℝ) := by
    have := (ptOk_sound hp8).1
    have e : (1 : ℝ) / (128 * (1 / 10240000)) = (((1 / 80000 : ℚ) : ℝ))⁻¹ := by push_cast; norm_num
    rw [e, Real.log_inv]
    push_cast at this ⊢
    linarith
  have hΘq0 : 0 ≤ e8Theta ((1 - 2 * q) / (2 * h)) := (e8Theta_pos (by linarith)).le
  have hT3 := corner_T3 (g := a + b - 2 * q) (by linarith) (by linarith) (by linarith) hbβ hXqb hXq
    hΘq0 hΘq hΘ128 hL80 (by norm_num)
  push_cast at hT3
  -- outer penalty
  have hlog : Real.log (((1 - 2 * q) / (2 * h)) / ((1 - 2 * c) / (2 * f))) =
      Real.log ((1 - 2 * q) / (1 - 2 * c)) + Real.log (f / h) := by
    have hq1 : (0 : ℝ) < 1 - 2 * q := by linarith
    have hc1' : (0 : ℝ) < 1 - 2 * c := by linarith
    rw [← Real.log_mul (div_pos hq1 hc1').ne' (div_pos hf0 hhpos).ne']
    congr 1
    field_simp
  rw [hlog] at hΘqc
  have hl1 : Real.log ((1 - 2 * q) / (1 - 2 * c)) ≤ 2 * (1 / 10000) / (1 - 2 * (1 / 10000)) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (1 - 2 * q) / (1 - 2 * c) by
      apply div_pos <;> linarith)
    have h1c : (1 - 2 * c) ≠ 0 := by linarith
    have e1 : (1 - 2 * q) / (1 - 2 * c) - 1 = 2 * (c - q) / (1 - 2 * c) := by
      field_simp; ring
    rw [e1] at this
    have h2 : 2 * (c - q) / (1 - 2 * c) ≤ 2 * (1 / 10000) / (1 - 2 * (1 / 10000)) := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      have hcq : c - q ≤ 1 / 10000 := by linarith
      have hcq0 : 0 ≤ c - q := by linarith
      nlinarith only [hcq, hcq0, hc1]
    linarith
  have hl2 : Real.log (f / h) ≤ ((LqHi : ℚ) : ℝ) := by
    have h1 : f / h ≤ 2 := by rw [div_le_iff₀ hhpos]; rw [hhdef]; linarith
    have h2 := Real.log_le_log (by positivity) h1
    linarith [hL.2]
  have hcb0 : 0 ≤ c - b := by linarith
  have hcbS : c - b ≤ 1 / 10000 := by linarith
  have hsum : 0 ≤ 2 * (1 / 10000 : ℝ) / (1 - 2 * (1 / 10000)) + ((LqHi : ℚ) : ℝ) := by
    have : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := by linarith [hL.2]
    positivity
  have hT4 := corner_T4 hcb0 hcbS hΘqc hl1 hl2 hsum
  -- combine
  have hfinR := rlt hfin
  push_cast at hfinR
  rw [hβ] at hfinR
  have e2 : (1 - 1 / 10000) - (1 - 2 * q) = 2 * q - 1 / 10000 := by ring
  have e3 : (1 - 2 * b) - (1 - 2 * c) = 2 * (c - b) := by ring
  rw [e2] at h2t
  rw [e3] at h3t
  have hre : (2 * q - 1 / 10000) * e8Theta ((1 - 2 * q) / (2 * h)) +
      (c - b) * e8Theta ((1 - 2 * c) / (2 * f)) =
      -((a + b - 2 * q) * e8Theta ((1 - 2 * q) / (2 * h))) -
        (c - b) * (e8Theta ((1 - 2 * q) / (2 * h)) - e8Theta ((1 - 2 * c) / (2 * f))) := by
    rw [hcdef]; ring
  linarith only [hT1', hj, h2t, h3t, hT3, hT4, hre, hfinR]

end CKLaneN1.Edge

end


