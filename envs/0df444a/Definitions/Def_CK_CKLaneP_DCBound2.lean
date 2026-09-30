-- Prove2me | Definitions.Def_CK_CKLaneP_DCBound2
-- name    : CK_CKLaneP_DCBound2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:54:32.281898+00:00
-- url     : https://prove2.me/theorems/092b15fe-2380-4c7c-803c-b2ec06eedeb9
-- title:
--   Courtade–Kumar proof module `CKLaneP.DCBound2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.DCBound2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.DCBound2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.DCBound2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/DCBound2.lean)

import Definitions.Def_CK_CKLaneP_SeamBase

-- ===== source module CKLaneP.DCBound2 =====
section
/-
Lane P — a sharper double-cap lower bound for large `β/p`.

The quadratic defect bound `H(m) − (H p + H q)/2 ≤ β²/(8 log2 · p(1−p))` (`H_mid_defect`) uses the
curvature at the left end `p`; for `β/p ≳ 1` it overestimates the defect by the factor
`≈ β/(p log(q/p))`.  The exact `x log x` part of the defect is
    (q·log(q/m) − p·log(m/p))/2,        m = (p+q)/2,
and the `(1−x) log(1−x)` part is `≤ β²/(4(1−q))` (`log y ≤ y − 1`).  This gives
`dc_lower_log2` and its cell-uniform form `dc_cell_lower2` used by the W/WK checkers.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- Sharp midpoint defect of `hn` (natural-log entropy). -/
theorem hn_mid_defect2 {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) :
    hn ((p + q) / 2) - (hn p + hn q) / 2 ≤
      (q * Real.log (q / ((p + q) / 2)) - p * Real.log (((p + q) / 2) / p)) / 2 +
        (q - p) ^ 2 / (4 * (1 - q)) := by
  obtain ⟨m, hm⟩ : ∃ m, m = (p + q) / 2 := ⟨_, rfl⟩
  rw [← hm]
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  have hm0 : 0 < m := by rw [hm]; linarith
  have hu1 : 0 < 1 - p := by linarith
  have hu2 : 0 < 1 - q := by linarith
  have hum : 0 < 1 - m := by rw [hm]; linarith
  have hid : hn m - (hn p + hn q) / 2 =
      (q * (Real.log q - Real.log m) - p * (Real.log m - Real.log p)) / 2 +
      ((1 - p) * (Real.log (1 - p) - Real.log (1 - m)) +
        (1 - q) * (Real.log (1 - q) - Real.log (1 - m))) / 2 := by
    unfold hn; rw [hm]; ring
  have e1 : Real.log (q / m) = Real.log q - Real.log m := Real.log_div hq0.ne' hm0.ne'
  have e2 : Real.log (m / p) = Real.log m - Real.log p := Real.log_div hm0.ne' hp.ne'
  have l1 : Real.log ((1 - p) / (1 - m)) ≤ (1 - p) / (1 - m) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have l2 : Real.log ((1 - q) / (1 - m)) ≤ (1 - q) / (1 - m) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have e3 : Real.log ((1 - p) / (1 - m)) = Real.log (1 - p) - Real.log (1 - m) :=
    Real.log_div hu1.ne' hum.ne'
  have e4 : Real.log ((1 - q) / (1 - m)) = Real.log (1 - q) - Real.log (1 - m) :=
    Real.log_div hu2.ne' hum.ne'
  rw [e3] at l1
  rw [e4] at l2
  have k1 := mul_le_mul_of_nonneg_left l1 hu1.le
  have k2 := mul_le_mul_of_nonneg_left l2 hu2.le
  have e5 : (1 - p) * ((1 - p) / (1 - m) - 1) + (1 - q) * ((1 - q) / (1 - m) - 1) =
      (q - p) ^ 2 / (2 * (1 - m)) := by
    have hum' : (1 - m) ≠ 0 := hum.ne'
    field_simp
    rw [hm]; ring
  have h6 : (q - p) ^ 2 / (2 * (1 - m)) ≤ (q - p) ^ 2 / (2 * (1 - q)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by rw [hm]; linarith)
  have h7 : (q - p) ^ 2 / (2 * (1 - q)) = 2 * ((q - p) ^ 2 / (4 * (1 - q))) := by
    field_simp; ring
  rw [hid, e1, e2]
  linarith

/-- Sharp midpoint defect of `H`. -/
theorem H_mid_defect2 {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) :
    H ((p + q) / 2) - (H p + H q) / 2 ≤
      ((q * Real.log (q / ((p + q) / 2)) - p * Real.log (((p + q) / 2) / p)) / 2 +
        (q - p) ^ 2 / (4 * (1 - q))) / Real.log 2 := by
  have hL := log_two_pos
  have h := hn_mid_defect2 hp hpq hq
  have eH : ∀ v : ℝ, H v = hn v / Real.log 2 := fun v => by
    rw [hn_eq_H_mul_log]; field_simp
  rw [eH, eH, eH]
  have e : hn ((p + q) / 2) / Real.log 2 - (hn p / Real.log 2 + hn q / Real.log 2) / 2 =
      (hn ((p + q) / 2) - (hn p + hn q) / 2) / Real.log 2 := by ring
  rw [e]
  exact div_le_div_of_nonneg_right h hL.le

/-- The subtracted gap·slope term, sharp form. -/
theorem dc_gap_slope_le2 {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1 / 2) :
    ((p + q) - 2 * entropyInverse ((H p + H q) / 2)) *
        radialSlope (entropyInverse ((H p + H q) / 2)) ≤
      2 * radialSlope p * ((((q * Real.log (q / ((p + q) / 2)) -
        p * Real.log (((p + q) / 2) / p)) / 2 + (q - p) ^ 2 / (4 * (1 - q))) / Real.log 2) /
          J ((p + q) / 2)) := by
  have hL := log_two_pos
  have hq0 : 0 < q := hp.trans hpq
  set hb := (H p + H q) / 2 with hhb
  set w := entropyInverse hb with hw
  set m := (p + q) / 2 with hm
  set δ := ((q * Real.log (q / m) - p * Real.log (m / p)) / 2 + (q - p) ^ 2 / (4 * (1 - q))) /
    Real.log 2 with hδ
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p < H q := H_strictMonoOn ⟨hp.le, by linarith⟩ ⟨hq0.le, hq.le⟩ hpq
  have hb0 : 0 < hb := by rw [hhb]; linarith
  have hb1 : hb ≤ 1 := by rw [hhb]; linarith [H_le_one q]
  obtain ⟨hw0, hw12, hHw⟩ := entropyInverse_spec hb0.le hb1
  have hpw : p ≤ w := by
    have h1 := entropyInverse_mono hHp.le hb1 (show H p ≤ hb by rw [hhb]; linarith)
    rwa [entropyInverse_H_lower hp.le (by linarith)] at h1
  have hbm : hb ≤ H m := entropy_average_le_midpoint hp.le (by linarith) hq0.le (by linarith)
  have hm12 : m < 1 / 2 := by rw [hm]; linarith
  have hwm : w ≤ m := by
    have h1 := entropyInverse_mono hb0.le (H_le_one m) hbm
    rwa [entropyInverse_H_lower (by rw [hm]; linarith) hm12.le] at h1
  have hwpos : 0 < w := lt_of_lt_of_le hp hpw
  have hwlt : w < 1 / 2 := lt_of_le_of_lt hwm hm12
  have hJm : 0 < J m := J_pos (by rw [hm]; linarith) hm12
  have hmono : MonotoneOn (fun t => H t - J m * t) (Icc w m) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc w m)
    · intro t ht
      exact ((Comparison.hasDerivAt_H (lt_of_lt_of_le hwpos ht.1) (by linarith [ht.2])).sub
        ((hasDerivAt_id t).const_mul (J m))).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((Comparison.hasDerivAt_H (lt_of_lt_of_le hwpos ht.1.le) (by linarith [ht.2])).sub
        ((hasDerivAt_id t).const_mul (J m))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hwpos ht.1.le
      have hd : HasDerivAt (fun t => H t - J m * t) (J t - J m * 1) t :=
        (Comparison.hasDerivAt_H ht0 (by linarith [ht.2])).sub ((hasDerivAt_id t).const_mul (J m))
      rw [hd.deriv]
      have := J_antitone ht0 hm12.le ht.2.le
      linarith
  have hmw := hmono ⟨le_rfl, hwm⟩ ⟨hwm, le_rfl⟩ hwm
  simp only at hmw
  have hdef := H_mid_defect2 hp hpq.le (by linarith : q < 1)
  rw [← hm] at hdef
  have hJmw : J m * (m - w) ≤ δ := by
    rw [hHw] at hmw
    rw [hδ]
    nlinarith
  have hgap : (p + q) - 2 * w ≤ 2 * (δ / J m) := by
    have e : (p + q) - 2 * w = 2 * (m - w) := by rw [hm]; ring
    rw [e]
    have : m - w ≤ δ / J m := by rw [le_div_iff₀ hJm, mul_comm]; exact hJmw
    linarith
  have hsl : radialSlope w ≤ radialSlope p :=
    ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ⟨hp, by linarith⟩ ⟨hwpos, hwlt⟩ hpw
  have hsl0 : 0 ≤ radialSlope w := by
    have hHw0 : 0 < H w := H_pos hwpos (by linarith)
    have hxw : (0 : ℝ) < (1 - 2 * w) / (2 * H w) := div_pos (by linarith) (mul_pos two_pos hHw0)
    have := e8Theta_pos hxw
    rw [theta_eq_radialSlope hxw] at this
    have hrc : radialContact (2 * ((1 - 2 * w) / (2 * H w))) 1 = w := by
      apply radialContact_eq_of_equation (mul_pos two_pos hxw) one_pos hwpos hwlt
      field_simp
    rw [hrc] at this
    exact this.le
  have hgap0 : 0 ≤ (p + q) - 2 * w := by linarith
  calc ((p + q) - 2 * w) * radialSlope w ≤ ((p + q) - 2 * w) * radialSlope p :=
        mul_le_mul_of_nonneg_left hsl hgap0
    _ ≤ (2 * (δ / J m)) * radialSlope p := mul_le_mul_of_nonneg_right hgap (hsl0.trans hsl)
    _ = 2 * radialSlope p * (δ / J m) := by ring

/-- Double-cap lower bound, sharp defect form. -/
theorem dc_lower_log2 {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1 / 2) :
    (q - p) * (Real.log (1 + (q - p) / p) / Real.log 2) / 2 -
        2 * radialSlope p * ((((q * Real.log (q / ((p + q) / 2)) -
          p * Real.log (((p + q) / 2) / p)) / 2 + (q - p) ^ 2 / (4 * (1 - q))) / Real.log 2) /
            J ((p + q) / 2)) ≤
      canonicalPureGap p q (H p) (H q) := by
  have hL := log_two_pos
  have hq0 : 0 < q := hp.trans hpq
  have hdc := dc_lower_w hp hpq hq.le
  have hGb := dc_gap_slope_le2 hp hpq hq
  have hic : (q - p) * (Real.log (1 + (q - p) / p) / Real.log 2) / 2 ≤ interiorCost p q := by
    unfold interiorCost
    have hJ : Real.log (1 + (q - p) / p) / Real.log 2 ≤ J p - J q := by
      unfold J
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ hL.le
      have e1 : 1 + (q - p) / p = q / p := by field_simp; ring
      have h1 : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
        Real.log_div (by linarith) hp.ne'
      have h2 : Real.log ((1 - q) / q) = Real.log (1 - q) - Real.log q :=
        Real.log_div (by linarith) hq0.ne'
      have h3 : Real.log (1 + (q - p) / p) = Real.log q - Real.log p := by
        rw [e1, Real.log_div hq0.ne' hp.ne']
      have h4 : Real.log (1 - q) ≤ Real.log (1 - p) := Real.log_le_log (by linarith) (by linarith)
      rw [h1, h2, h3]
      linarith
    have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ q - p)
    linarith
  linarith

/-- Cell-uniform sharp double-cap lower bound (real form; the rational checkers supply the
logarithm bounds `LA ≤ log((p0+blo)/p1)`, `log(2qd/(qd+p0)) ≤ LB`, `LC ≤ log((p1+p0+blo)/(2p1))`). -/
theorem dc_cell_lower2 {p q p0 p1 blo bhi qd rs0 Jq l2hi l2lo LA LB LC : ℝ}
    (hp0 : 0 < p0) (hp0p : p0 ≤ p) (hpp1 : p ≤ p1) (hpq : p < q) (hqqd : q ≤ qd) (hqd : qd < 1 / 2)
    (hblo0 : 0 ≤ blo) (hblo : blo ≤ q - p) (hbhi : q - p ≤ bhi)
    (hJq : Jq ≤ J q) (hJq0 : 0 < Jq) (hrs : radialSlope p ≤ rs0)
    (hl2hi : Real.log 2 ≤ l2hi) (hl2lo : l2lo ≤ Real.log 2) (hl2lo0 : 0 < l2lo)
    (hLA : LA ≤ Real.log ((p0 + blo) / p1)) (hLB : Real.log (2 * qd / (qd + p0)) ≤ LB)
    (hLC : LC ≤ Real.log ((p1 + p0 + blo) / (2 * p1))) :
    blo * max 0 LA / (2 * l2hi) -
        2 * rs0 * (((qd * LB / 2 - p0 * max 0 LC / 2) + bhi ^ 2 / (4 * (1 - qd))) / l2lo) / Jq ≤
      canonicalPureGap p q (H p) (H q) := by
  have hp : 0 < p := lt_of_lt_of_le hp0 hp0p
  have hq0 : 0 < q := hp.trans hpq
  have hq : q < 1 / 2 := lt_of_le_of_lt hqqd hqd
  have hL := log_two_pos
  have hdc := dc_lower_log2 hp hpq hq
  have hp1 : 0 < p1 := lt_of_lt_of_le hp hpp1
  set m := (p + q) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  -- interior term
  have hqp : 1 + (q - p) / p = q / p := by field_simp; ring
  have hlogqp0 : 0 ≤ Real.log (q / p) := Real.log_nonneg (by rw [le_div_iff₀ hp]; linarith)
  have hA : max 0 LA ≤ Real.log (q / p) := by
    apply max_le hlogqp0
    refine le_trans hLA (Real.log_le_log (by positivity) ?_)
    rw [div_le_div_iff₀ hp1 hp]
    nlinarith [mul_le_mul_of_nonneg_right (show p0 + blo ≤ q by linarith) hp.le,
      mul_le_mul_of_nonneg_left hpp1 hq0.le]
  have hI : blo * max 0 LA / (2 * l2hi) ≤ (q - p) * (Real.log (1 + (q - p) / p) / Real.log 2) / 2 := by
    rw [hqp]
    have h1 : blo * max 0 LA ≤ (q - p) * Real.log (q / p) :=
      mul_le_mul hblo hA (le_max_left _ _) (by linarith)
    have h2 : (q - p) * Real.log (q / p) / (2 * l2hi) ≤ (q - p) * Real.log (q / p) / (2 * Real.log 2) :=
      div_le_div_of_nonneg_left (mul_nonneg (by linarith) hlogqp0) (by positivity) (by linarith)
    have h3 : blo * max 0 LA / (2 * l2hi) ≤ (q - p) * Real.log (q / p) / (2 * l2hi) :=
      div_le_div_of_nonneg_right h1 (by linarith)
    have e : (q - p) * (Real.log (q / p) / Real.log 2) / 2 = (q - p) * Real.log (q / p) / (2 * Real.log 2) := by
      field_simp
    rw [e]; linarith
  -- defect term: q log(q/m) ≤ qd·LB, p log(m/p) ≥ p0·max 0 LC
  have hqm1 : 1 ≤ q / m := by rw [le_div_iff₀ hm0, hm]; linarith
  have hlqm0 : 0 ≤ Real.log (q / m) := Real.log_nonneg hqm1
  have hqm : q / m ≤ 2 * qd / (qd + p0) := by
    rw [hm, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul hqqd hp0p hp0.le (by linarith : (0 : ℝ) ≤ qd)]
  have hB1 : q * Real.log (q / m) ≤ qd * LB := by
    have h1 : Real.log (q / m) ≤ LB := le_trans (Real.log_le_log (by positivity) hqm) hLB
    exact mul_le_mul hqqd h1 hlqm0 (by linarith)
  have hmp1 : 1 ≤ m / p := by rw [le_div_iff₀ hp, hm]; linarith
  have hlmp0 : 0 ≤ Real.log (m / p) := Real.log_nonneg hmp1
  have hmp : (p1 + p0 + blo) / (2 * p1) ≤ m / p := by
    rw [hm, div_le_div_iff₀ (by positivity) hp]
    nlinarith [mul_le_mul_of_nonneg_right (show p0 + blo ≤ q by linarith) hp.le,
      mul_le_mul_of_nonneg_left hpp1 hq0.le]
  have hC1 : p0 * max 0 LC ≤ p * Real.log (m / p) := by
    have h1 : max 0 LC ≤ Real.log (m / p) :=
      max_le hlmp0 (le_trans hLC (Real.log_le_log (by positivity) hmp))
    exact mul_le_mul hp0p h1 (le_max_left _ _) hp.le
  have hβ2 : (q - p) ^ 2 / (4 * (1 - q)) ≤ bhi ^ 2 / (4 * (1 - qd)) := by
    have hb2 : (q - p) ^ 2 ≤ bhi ^ 2 := pow_le_pow_left₀ (by linarith) hbhi 2
    calc (q - p) ^ 2 / (4 * (1 - q)) ≤ bhi ^ 2 / (4 * (1 - q)) :=
          div_le_div_of_nonneg_right hb2 (by linarith)
      _ ≤ bhi ^ 2 / (4 * (1 - qd)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  set Dt := (q * Real.log (q / m) - p * Real.log (m / p)) / 2 + (q - p) ^ 2 / (4 * (1 - q)) with hDt
  set Db := (qd * LB / 2 - p0 * max 0 LC / 2) + bhi ^ 2 / (4 * (1 - qd)) with hDb
  have hDtb : Dt ≤ Db := by rw [hDt, hDb]; linarith
  have hDt0 : 0 ≤ Dt := by
    have hdef0 : 0 ≤ H m - (H p + H q) / 2 := by
      have := entropy_average_le_midpoint hp.le (by linarith) hq0.le (by linarith)
      rw [hm]; linarith
    have hdef := H_mid_defect2 hp hpq.le (by linarith : q < 1)
    rw [← hm] at hdef
    have h2 : 0 ≤ Dt / Real.log 2 := le_trans hdef0 hdef
    have h3 : Dt = Dt / Real.log 2 * Real.log 2 := by field_simp
    rw [h3]
    exact mul_nonneg h2 hL.le
  have hDl : Dt / Real.log 2 ≤ Db / l2lo := by
    calc Dt / Real.log 2 ≤ Db / Real.log 2 := div_le_div_of_nonneg_right hDtb hL.le
      _ ≤ Db / l2lo := div_le_div_of_nonneg_left (le_trans hDt0 hDtb) hl2lo0 hl2lo
  have hJm : Jq ≤ J m := by
    have := J_antitone hm0 hq.le (show m ≤ q by rw [hm]; linarith)
    linarith
  have hrs0 : 0 ≤ radialSlope p := by
    have hHp0 : 0 < H p := H_pos hp (by linarith)
    have hxp : (0 : ℝ) < (1 - 2 * p) / (2 * H p) := div_pos (by linarith) (mul_pos two_pos hHp0)
    have := e8Theta_pos hxp
    rw [theta_eq_radialSlope hxp] at this
    have hrc : radialContact (2 * ((1 - 2 * p) / (2 * H p))) 1 = p := by
      apply radialContact_eq_of_equation (mul_pos two_pos hxp) one_pos hp (by linarith)
      field_simp
    rw [hrc] at this
    exact this.le
  have hJm0 : 0 < J m := lt_of_lt_of_le hJq0 hJm
  have hX : 2 * radialSlope p * (Dt / Real.log 2 / J m) ≤ 2 * rs0 * (Db / l2lo) / Jq := by
    have h1 : Dt / Real.log 2 / J m ≤ Db / l2lo / Jq := by
      calc Dt / Real.log 2 / J m ≤ Db / l2lo / J m :=
            div_le_div_of_nonneg_right hDl hJm0.le
        _ ≤ Db / l2lo / Jq :=
            div_le_div_of_nonneg_left (div_nonneg (le_trans hDt0 hDtb) hl2lo0.le) hJq0 hJm
    have h2 : 0 ≤ Dt / Real.log 2 / J m := div_nonneg (div_nonneg hDt0 hL.le) hJm0.le
    calc 2 * radialSlope p * (Dt / Real.log 2 / J m) ≤ 2 * rs0 * (Dt / Real.log 2 / J m) :=
          mul_le_mul_of_nonneg_right (by linarith) h2
      _ ≤ 2 * rs0 * (Db / l2lo / Jq) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 2 * rs0 * (Db / l2lo) / Jq := by ring
  have hdc' : (q - p) * (Real.log (1 + (q - p) / p) / Real.log 2) / 2 -
      2 * radialSlope p * (Dt / Real.log 2 / J m) ≤ canonicalPureGap p q (H p) (H q) := hdc
  linarith

end CKLaneP

end


