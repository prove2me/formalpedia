-- Prove2me | Definitions.Def_CK_CKLaneP_SeamBase
-- name    : CK_CKLaneP_SeamBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:36:19.110985+00:00
-- url     : https://prove2.me/theorems/ebfa2b60-9380-4684-89fa-38a8f2db97b4
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamBase.lean)

import Definitions.Def_CK_CKLaneP_SeamDip
import Definitions.Def_CK_CKLaneP_DCBound
import Definitions.Def_CK_CKLaneP_ThetaBulk

-- ===== source module CKLaneP.SeamBase =====
section
/-
Lane P — lower bounds for the seam base value `s(y_lo)`.

Case A (`q ≤ S/2`, `y_lo = 0`):  s(0) = emLine e f (S/2)
    ≥ cPG(p,q,e,f) + [c1·β − (c2/2)·β²] + (S/2 − q)·ℓ,
Case B (`q > S/2`, `y_lo = 2q − S`):  s(2q−S) = cPG(S−q, q, e, f)
    ≥ cPG(p,q,e,f) + [c1·L − (c2/2)(β² − (β−L)²)],   L = S − q − p,
where `c1 − c2(q−t) ≤ rightD q e f t` on the right fiber and `ℓ ≤ jdef e f m` on `[q, S/2]`.

* `rightFiber_affine` : affine-derivative mean-value bound on the right fiber (endpoint `b` allowed).
* `rightD_ge`         : `rightD ≥ Pm·log(E/(2e)) − 12(q−t)/E`   (Pm ≤ profile on the contacts).
* `jdef_ge_log`       : `jdef ≥ Pm·log(E/(2e)) − PM·log(2f/E)`.
* `dc_lower_log`      : `DC ≥ β·log(1+β/p)/(2 log 2) − β²·rs(p)/(4 log 2·p(1−p)·J(m))`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

theorem seamCurve_zero (S e f : ℝ) : seamCurve S e f 0 = emLine e f (S / 2) := by
  simp [seamCurve, emLine]

theorem seamCurve_ylo (S e f q : ℝ) :
    seamCurve S e f (2 * q - S) = canonicalPureGap (S - q) q e f := by
  unfold seamCurve
  have h1 : (S - (2 * q - S)) / 2 = S - q := by ring
  have h2 : (S + (2 * q - S)) / 2 = q := by ring
  rw [h1, h2]

/-- Affine mean-value bound on the right fiber `x ↦ cPG(x, b, H a, H b)` over `[t1, t2] ⊆ [a, b]`. -/
theorem rightFiber_affine {a b t1 t2 c1 c2 : ℝ} (ha : 0 < a) (hat1 : a ≤ t1) (h12 : t1 ≤ t2)
    (h2b : t2 ≤ b) (hb : b ≤ 1 / 2)
    (hd : ∀ t ∈ Ioo t1 t2, c1 - c2 * (b - t) ≤ rightD b (H a) (H b) t) :
    canonicalPureGap t1 b (H a) (H b) + c1 * (t2 - t1) - c2 * ((b - t1) ^ 2 - (b - t2) ^ 2) / 2 ≤
      canonicalPureGap t2 b (H a) (H b) := by
  have hab : a ≤ b := le_trans hat1 (le_trans h12 h2b)
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hHb : 0 < H b := lt_of_lt_of_le hHa
    (H_strictMonoOn.monotoneOn ⟨ha.le, by linarith⟩ ⟨ha.le.trans hab, hb⟩ hab)
  have hcont0 := continuousOn_rightFiber ha hab hb
  have hcont : ContinuousOn (fun t => canonicalPureGap t b (H a) (H b) - c1 * t - c2 * (b - t) ^ 2 / 2)
      (Icc t1 t2) := by
    have h1 : ContinuousOn (fun t => canonicalPureGap t b (H a) (H b)) (Icc t1 t2) :=
      hcont0.mono (Icc_subset_Icc hat1 h2b)
    have h2 : ContinuousOn (fun t : ℝ => c1 * t) (Icc t1 t2) := by fun_prop
    have h3 : ContinuousOn (fun t : ℝ => c2 * (b - t) ^ 2 / 2) (Icc t1 t2) := by fun_prop
    exact (h1.sub h2).sub h3
  have hderiv : ∀ t ∈ Ioo t1 t2, HasDerivAt
      (fun t => canonicalPureGap t b (H a) (H b) - c1 * t - c2 * (b - t) ^ 2 / 2)
      (rightD b (H a) (H b) t - c1 + c2 * (b - t)) t := by
    intro t ht
    have htb : t < b := lt_of_lt_of_le ht.2 h2b
    have h := hasDerivAt_rightFiber htb (by linarith) (by linarith) hHa hHb
    have hq := ((((hasDerivAt_id t).const_sub b).pow 2).const_mul c2).div_const 2
    have h2 := (hasDerivAt_id t).const_mul c1
    refine ((h.sub h2).sub hq).congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat]
    unfold rightD
    ring
  have hmono : MonotoneOn
      (fun t => canonicalPureGap t b (H a) (H b) - c1 * t - c2 * (b - t) ^ 2 / 2) (Icc t1 t2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t1 t2) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      have := hd t ht
      linarith
  have h := hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  simp only at h
  nlinarith

/-- `(b − t)/E ≤ 2/25` on the right fiber (`b ≤ 1/10000`). -/
theorem gap_over_E_small {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1 / 10000) :
    (b - t) / (H a + H b) ≤ 2 / 25 := by
  have hb0 : 0 < b := lt_of_lt_of_le ha (hat.trans htb)
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hJb : 13 ≤ J b := by
    have h1 := J_ten_thousandth_ge
    have h2 := J_antitone hb0 (by norm_num : (1 : ℝ) / 10000 ≤ 1 / 2) hb
    linarith
  have hHb : J b * b ≤ H b := by
    have := J_mul_le_H_sub (le_refl (0 : ℝ)) hb0.le (by linarith)
    simp only [H_zero, sub_zero] at this
    linarith
  have hHb0 : 0 < H b := lt_of_lt_of_le (mul_pos (by linarith) hb0) hHb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Lower bound of the right-fiber derivative in logarithmic form. -/
theorem rightD_ge {a b t Pm : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t < b) (hb : b ≤ 1 / 10000)
    (hPm0 : 0 ≤ Pm)
    (hP : ∀ x ∈ Icc ((1 - t - b) / (H a + H b)) ((1 - 2 * t) / (2 * H a)),
      Pm ≤ profile (radialContact (2 * x) 1)) :
    Pm * Real.log ((H a + H b) / (2 * H a)) - 12 * ((b - t) / (H a + H b)) ≤
      rightD b (H a) (H b) t := by
  have hb0 : 0 < b := lt_of_lt_of_le ha (hat.trans htb.le)
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hab : a ≤ b := hat.trans htb.le
  have hHab : H a ≤ H b := H_strictMonoOn.monotoneOn ⟨ha.le, by linarith⟩ ⟨hb0.le, by linarith⟩ hab
  have hE : 0 < H a + H b := by linarith
  have hV : 0 < (1 - t - b) / (H a + H b) := div_pos (by linarith) hE
  have hVW : (1 - t - b) / (H a + H b) ≤ (1 - 2 * t) / (2 * H a) := by
    rw [div_le_div_iff₀ hE (by linarith)]
    have h1 : (1 - t - b) * (2 * H a) ≤ (1 - 2 * t) * (2 * H a) := by nlinarith
    have h2 : (1 - 2 * t) * (2 * H a) ≤ (1 - 2 * t) * (H a + H b) := by nlinarith
    linarith
  have hlog := theta_log_ge hV hVW hP
  have hratio : (H a + H b) / (2 * H a) ≤ (1 - 2 * t) / (2 * H a) / ((1 - t - b) / (H a + H b)) := by
    have hVp : 0 < 1 - t - b := by linarith
    have e : (1 - 2 * t) / (2 * H a) / ((1 - t - b) / (H a + H b)) =
        (H a + H b) / (2 * H a) * ((1 - 2 * t) / (1 - t - b)) := by
      field_simp
    rw [e]
    have h1 : 1 ≤ (1 - 2 * t) / (1 - t - b) := by rw [le_div_iff₀ hVp]; linarith
    have h0 : 0 ≤ (H a + H b) / (2 * H a) := by positivity
    nlinarith
  have hlogmono : Real.log ((H a + H b) / (2 * H a)) ≤
      Real.log ((1 - 2 * t) / (2 * H a) / ((1 - t - b) / (H a + H b))) :=
    Real.log_le_log (by positivity) hratio
  have h12 := theta_le_twelve (show 0 < (b - t) / (H a + H b) from div_pos (by linarith) hE)
    (gap_over_E_small ha hat htb.le hb)
  unfold rightD
  have := mul_le_mul_of_nonneg_left hlogmono hPm0
  linarith

/-- Logarithmic lower bound of the bulk integrand. -/
theorem jdef_ge_log {e f m Pm PM : ℝ} (he : 0 < e) (hef : e ≤ f) (hm : m < 1 / 2)
    (hPm : ∀ x ∈ Icc ((1 - 2 * m) / (e + f)) ((1 - 2 * m) / (2 * e)),
      Pm ≤ profile (radialContact (2 * x) 1))
    (hPM : ∀ x ∈ Icc ((1 - 2 * m) / (2 * f)) ((1 - 2 * m) / (e + f)),
      profile (radialContact (2 * x) 1) ≤ PM) :
    Pm * Real.log ((e + f) / (2 * e)) - PM * Real.log (2 * f / (e + f)) ≤ jdef e f m := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  have hZ : 0 < 1 - 2 * m := by linarith
  have hE : 0 < e + f := by linarith
  have h1 : (1 - 2 * m) / (e + f) ≤ (1 - 2 * m) / (2 * e) :=
    div_le_div_of_nonneg_left hZ.le (by linarith) (by linarith)
  have h2 : (1 - 2 * m) / (2 * f) ≤ (1 - 2 * m) / (e + f) :=
    div_le_div_of_nonneg_left hZ.le hE (by linarith)
  have hA := theta_log_ge (div_pos hZ hE) h1 hPm
  have hB := theta_log_le (div_pos hZ (by linarith)) h2 hPM
  have r1 : (1 - 2 * m) / (2 * e) / ((1 - 2 * m) / (e + f)) = (e + f) / (2 * e) := by
    field_simp
  have r2 : (1 - 2 * m) / (e + f) / ((1 - 2 * m) / (2 * f)) = 2 * f / (e + f) := by
    field_simp
  rw [r1] at hA
  rw [r2] at hB
  unfold jdef
  linarith

/-- The subtracted gap·slope term of the tangent-line double-cap bound. -/
theorem dc_gap_slope_le {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1 / 2) :
    ((p + q) - 2 * entropyInverse ((H p + H q) / 2)) *
        radialSlope (entropyInverse ((H p + H q) / 2)) ≤
      (q - p) ^ 2 * (radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J ((p + q) / 2))) := by
  have hL := log_two_pos
  have hq0 : 0 < q := hp.trans hpq
  have hpp : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hqq : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  set hb := (H p + H q) / 2 with hhb
  set w := entropyInverse hb with hw
  set m := (p + q) / 2 with hm
  -- facts on w
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
  -- p + q - 2w bound
  have hgap : (p + q) - 2 * w ≤ (q - p) ^ 2 / (4 * (Real.log 2 * (p * (1 - p))) * J m) := by
    have hdef := H_mid_defect hp hpq.le hq.le
    -- J(m)(m - w) ≤ H m - H w
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
        have hderv : deriv (fun t => H t - J m * t) t = J t - J m * 1 := hd.deriv
        rw [hderv]
        have := J_antitone ht0 hm12.le ht.2.le
        linarith
    have hmw := hmono ⟨le_rfl, hwm⟩ ⟨hwm, le_rfl⟩ hwm
    simp only at hmw
    try rw [hHw] at hmw
    -- J m (m - w) ≤ H m - hb ≤ defect
    have hJmw : J m * (m - w) ≤ (q - p) ^ 2 / (8 * (Real.log 2 * (p * (1 - p)))) := by
      rw [← hm] at hdef
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    have e : (p + q) - 2 * w = 2 * (m - w) := by rw [hm]; ring
    rw [e]
    have h1p : (1 - p) ≠ 0 := by linarith
    have hXp : 0 < 8 * (Real.log 2 * (p * (1 - p))) := by positivity
    have e2 : (q - p) ^ 2 / (8 * (Real.log 2 * (p * (1 - p)))) * (8 * (Real.log 2 * (p * (1 - p)))) =
        (q - p) ^ 2 := div_mul_cancel₀ _ hXp.ne'
    have h8 := mul_le_mul_of_nonneg_right hJmw hXp.le
    rw [e2] at h8
    nlinarith [h8]
  -- radialSlope w ≤ radialSlope p
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
  have hprod : ((p + q) - 2 * w) * radialSlope w ≤
      (q - p) ^ 2 / (4 * (Real.log 2 * (p * (1 - p))) * J m) * radialSlope p := by
    calc ((p + q) - 2 * w) * radialSlope w ≤ ((p + q) - 2 * w) * radialSlope p :=
          mul_le_mul_of_nonneg_left hsl hgap0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgap (hsl0.trans hsl)
  have e4 : (q - p) ^ 2 / (4 * (Real.log 2 * (p * (1 - p))) * J m) * radialSlope p =
      (q - p) ^ 2 * (radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J m)) := by ring
  rw [e4] at hprod
  exact hprod

/-- Double-cap lower bound with the exact logarithm in the interior cost. -/
theorem dc_lower_log {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1 / 2) :
    (q - p) * (Real.log (1 + (q - p) / p) / Real.log 2) / 2 -
        (q - p) ^ 2 * (radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J ((p + q) / 2))) ≤
      canonicalPureGap p q (H p) (H q) := by
  have hL := log_two_pos
  have hq0 : 0 < q := hp.trans hpq
  have hdc := dc_lower_w hp hpq hq.le
  have hGb := dc_gap_slope_le hp hpq hq
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

end CKLaneP

end


