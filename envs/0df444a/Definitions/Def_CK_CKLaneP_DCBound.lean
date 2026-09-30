-- Prove2me | Definitions.Def_CK_CKLaneP_DCBound
-- name    : CK_CKLaneP_DCBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:09:22.902409+00:00
-- url     : https://prove2.me/theorems/c252c29d-ad54-4a77-939f-974dc2786b33
-- title:
--   Courtade–Kumar proof module `CKLaneP.DCBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.DCBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.DCBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.DCBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/DCBound.lean)

import Definitions.Def_CK_CKLaneP_SeamCore
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge

-- ===== source module CKLaneP.DCBound =====
section
/-
Lane P — quantitative lower bounds for the double-cap value `DC(p,q) = cPG(p, q, H p, H q)`.

* `dc_lower_w`          : DC ≥ interiorCost p q − (p+q−2w)·radialSlope w,  w = Hinv((Hp+Hq)/2)
                          (tangent-line bound of the convex radial function at the cap radius 1−2w).
* `J_sub_ge`, `J_sub_le`: mean-value bounds for `J` (|J'| = 1/(log 2 · v(1−v))).
* `H_mid_defect`        : H((p+q)/2) − (Hp+Hq)/2 ≤ (q−p)²/(8 log 2 · p(1−p)).
* `dc_lower_normalized` : DC ≥ (q−p)²·[1/(2 log2 q(1−q)) − radialSlope p/(4 log2 p(1−p) J((p+q)/2))].
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set

theorem dc_lower_w {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1 / 2) :
    interiorCost p q - ((p + q) - 2 * entropyInverse ((H p + H q) / 2)) *
        radialSlope (entropyInverse ((H p + H q) / 2)) ≤ canonicalPureGap p q (H p) (H q) := by
  set hb := (H p + H q) / 2 with hhb
  set w := entropyInverse hb with hw
  set m := (p + q) / 2 with hm
  have hp12 : p < 1 / 2 := lt_of_lt_of_le hpq hq
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p < H q := H_strictMonoOn ⟨hp.le, hp12.le⟩ ⟨(hp.trans hpq).le, hq⟩ hpq
  have hHq1 : H q ≤ 1 := H_le_one q
  have hb0 : 0 < hb := by rw [hhb]; linarith
  have hb1 : hb < 1 := by rw [hhb]; linarith
  obtain ⟨hw0, hw12, hHw⟩ := entropyInverse_spec hb0.le hb1.le
  have hwpos : 0 < w := entropyInverse_pos hb0 hb1.le
  have hwlt : w < 1 / 2 := by
    rcases lt_or_eq_of_le hw12 with h | h
    · exact h
    · exfalso; rw [h, H_half] at hHw; linarith
  have hbm : hb ≤ H m := entropy_average_le_midpoint hp.le (by linarith) (hp.trans hpq).le (by linarith)
  have hm12 : m ≤ 1 / 2 := by rw [hm]; linarith
  have hwm : w ≤ m := by
    have h1 := entropyInverse_mono hb0.le (H_le_one m) hbm
    rwa [entropyInverse_H_lower (by rw [hm]; linarith) hm12] at h1
  rw [canonicalPureGap_doubleCap_eq hp hpq.le hq]
  -- phi m hb = F(1-2w) - F(1-2m)
  have hcap := phi_at_entropy_cap hwpos hwlt.le
  rw [hHw] at hcap
  have hphi : phi m hb = F (1 - 2 * w) hb - F (1 - 2 * m) hb := by
    unfold phi at hcap ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * m)]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * w)] at hcap
    linarith
  have hsum : m + m = p + q := by rw [hm]; ring
  have hkey : phi m hb ≤ ((p + q) - 2 * w) * radialSlope w := by
    rw [hphi]
    rcases eq_or_lt_of_le hwm with heq | hlt
    · rw [heq, sub_self, show p + q - 2 * m = 0 by linarith, zero_mul]
    · have hconv := convexOn_F_radius hb0
      have hx : (1 - 2 * m) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
      have hy : (1 - 2 * w) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
      have hxy : 1 - 2 * m < 1 - 2 * w := by linarith
      have hdiff := (hasDerivAt_F_radius (show 0 < 1 - 2 * w by linarith) hb0).differentiableAt
      have hsl := hconv.slope_le_deriv hx hy hxy hdiff
      rw [deriv_F_radius_slope (by linarith) hb0] at hsl
      have hrc : radialContact (1 - 2 * w) hb = w := by
        rw [← hHw]; exact radialContact_H_lower hwpos hwlt
      rw [hrc, slope_def_field] at hsl
      have hpos : 0 < (1 - 2 * w) - (1 - 2 * m) := by linarith
      rw [div_le_iff₀ hpos] at hsl
      have e : radialSlope w * (1 - 2 * w - (1 - 2 * m)) = (p + q - 2 * w) * radialSlope w := by
        rw [← hsum]; ring
      linarith
  linarith

/-- `J p − J q ≥ (q − p)/(log 2 · q(1−q))` for `0 < p < q ≤ 1/2`. -/
theorem J_sub_ge {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ 1 / 2) :
    (q - p) / (Real.log 2 * (q * (1 - q))) ≤ J p - J q := by
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  have hL := log_two_pos
  have hqq : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  set κ := 1 / (Real.log 2 * (q * (1 - q))) with hκ
  have hanti : AntitoneOn (fun t => J t + κ * t) (Icc p q) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc p q)
    · intro t ht
      exact ((hasDerivAt_J (lt_of_lt_of_le hp ht.1) (by linarith [ht.2])).add
        ((hasDerivAt_id t).const_mul κ)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hasDerivAt_J (lt_of_lt_of_le hp ht.1.le) (by linarith [ht.2])).add
        ((hasDerivAt_id t).const_mul κ)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hp ht.1.le
      have hd : HasDerivAt (fun t => J t + κ * t) (-1 / (Real.log 2 * t * (1 - t)) + κ * 1) t :=
        (hasDerivAt_J ht0 (by linarith [ht.2])).add ((hasDerivAt_id t).const_mul κ)
      have hderv : deriv (fun t => J t + κ * t) t = -1 / (Real.log 2 * t * (1 - t)) + κ * 1 := hd.deriv
      rw [hderv]
      have htt : 0 < t * (1 - t) := mul_pos ht0 (by linarith [ht.2])
      have hle : t * (1 - t) ≤ q * (1 - q) := by nlinarith [ht.2]
      rw [hκ, mul_one]
      have h1 : 1 / (Real.log 2 * (q * (1 - q))) ≤ 1 / (Real.log 2 * t * (1 - t)) := by
        apply one_div_le_one_div_of_le (by rw [mul_assoc]; exact mul_pos hL htt)
        have := mul_le_mul_of_nonneg_left hle hL.le
        nlinarith
      have h2 : -1 / (Real.log 2 * t * (1 - t)) = -(1 / (Real.log 2 * t * (1 - t))) := by ring
      rw [h2]
      linarith
  have key : J q + κ * q ≤ J p + κ * p := hanti ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
  have e : (q - p) / (Real.log 2 * (q * (1 - q))) = κ * q - κ * p := by
    rw [hκ]; field_simp
  linarith

/-- `J u − J v ≤ (v − u)/(log 2 · u(1−u))` for `0 < u ≤ v ≤ 1/2`. -/
theorem J_sub_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1 / 2) :
    J u - J v ≤ (v - u) / (Real.log 2 * (u * (1 - u))) := by
  have hL := log_two_pos
  have huu : 0 < u * (1 - u) := mul_pos hu (by linarith)
  set κ := 1 / (Real.log 2 * (u * (1 - u))) with hκ
  have hmono : MonotoneOn (fun t => J t + κ * t) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
    · intro t ht
      exact ((hasDerivAt_J (lt_of_lt_of_le hu ht.1) (by linarith [ht.2])).add
        ((hasDerivAt_id t).const_mul κ)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hasDerivAt_J (lt_of_lt_of_le hu ht.1.le) (by linarith [ht.2])).add
        ((hasDerivAt_id t).const_mul κ)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hu ht.1.le
      have hd : HasDerivAt (fun t => J t + κ * t) (-1 / (Real.log 2 * t * (1 - t)) + κ * 1) t :=
        (hasDerivAt_J ht0 (by linarith [ht.2])).add ((hasDerivAt_id t).const_mul κ)
      have hderv : deriv (fun t => J t + κ * t) t = -1 / (Real.log 2 * t * (1 - t)) + κ * 1 := hd.deriv
      rw [hderv]
      have htt : 0 < t * (1 - t) := mul_pos ht0 (by linarith [ht.2])
      have hle : u * (1 - u) ≤ t * (1 - t) := by nlinarith [ht.1, ht.2]
      rw [hκ, mul_one]
      have h1 : 1 / (Real.log 2 * t * (1 - t)) ≤ 1 / (Real.log 2 * (u * (1 - u))) := by
        apply one_div_le_one_div_of_le (by positivity)
        have := mul_le_mul_of_nonneg_left hle hL.le
        nlinarith
      have h2 : -1 / (Real.log 2 * t * (1 - t)) = -(1 / (Real.log 2 * t * (1 - t))) := by ring
      rw [h2]
      linarith
  have key : J u + κ * u ≤ J v + κ * v := hmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  have e : (v - u) / (Real.log 2 * (u * (1 - u))) = κ * v - κ * u := by
    rw [hκ]; field_simp
  linarith

/-- Midpoint concavity defect of `H`. -/
theorem H_mid_defect {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ 1 / 2) :
    H ((p + q) / 2) - (H p + H q) / 2 ≤ (q - p) ^ 2 / (8 * (Real.log 2 * (p * (1 - p)))) := by
  have hL := log_two_pos
  have hpp : 0 < p * (1 - p) := mul_pos hp (by linarith)
  set m := (p + q) / 2 with hm
  set κ := 1 / (Real.log 2 * (p * (1 - p))) with hκ
  set d := (q - p) / 2 with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  -- g(t) = 2H(m) - H(m-t) - H(m+t) - κ t², antitone on [0, d]
  have hanti : AntitoneOn (fun t => 2 * H m - H (m - t) - H (m + t) - κ * t ^ 2) (Icc 0 d) := by
    have hder : ∀ t ∈ Icc 0 d, HasDerivAt (fun t => 2 * H m - H (m - t) - H (m + t) - κ * t ^ 2)
        (J (m - t) - J (m + t) - κ * (2 * t)) t := by
      intro t ht
      have h1 : 0 < m - t := by rw [hm]; linarith [ht.2, hd]
      have h2 : m + t < 1 := by rw [hm]; linarith [ht.2, hd]
      have hA := (Comparison.hasDerivAt_H h1 (by linarith [ht.1])).comp t ((hasDerivAt_id t).const_sub m)
      have hB := (Comparison.hasDerivAt_H (by linarith [ht.1]) h2).comp t ((hasDerivAt_id t).const_add m)
      have hC := ((hasDerivAt_id t).pow 2).const_mul κ
      have := (((hasDerivAt_const t (2 * H m)).sub hA).sub hB).sub hC
      refine this.congr_deriv ?_
      simp only [id_eq, Nat.cast_ofNat]
      ring
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 d)
    · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hder t ht').deriv]
      have h1 : 0 < m - t := by rw [hm]; linarith [ht'.2, hd]
      have hmt : m + t ≤ 1 / 2 := by rw [hm]; linarith [ht'.2, hd]
      have hJ := J_sub_le h1 (by linarith [ht'.1]) hmt
      have hrat : ((m + t) - (m - t)) / (Real.log 2 * ((m - t) * (1 - (m - t)))) ≤ κ * (2 * t) := by
        rw [hκ]
        have hle : p * (1 - p) ≤ (m - t) * (1 - (m - t)) := by
          have hpm : p ≤ m - t := by rw [hm]; linarith [ht'.2, hd]
          have h3 : 0 ≤ 1 - (m - t) - p := by rw [hm]; linarith [ht'.1]
          nlinarith [mul_nonneg (sub_nonneg.2 hpm) h3]
        have hpos : 0 < (m - t) * (1 - (m - t)) := mul_pos h1 (by linarith [ht'.1])
        rw [show (m + t) - (m - t) = 2 * t by ring]
        rw [div_le_iff₀ (by positivity)]
        have : 1 / (Real.log 2 * (p * (1 - p))) * (Real.log 2 * ((m - t) * (1 - (m - t)))) ≥ 1 := by
          rw [ge_iff_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith [ht'.1]
      linarith
  have hg := hanti ⟨le_rfl, hd0⟩ ⟨hd0, le_rfl⟩ hd0
  simp only [sub_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero] at hg
  have hmp : m - d = p := by rw [hm, hd]; ring
  have hmq : m + d = q := by rw [hm, hd]; ring
  rw [hmp, hmq] at hg
  have e : κ * d ^ 2 = (q - p) ^ 2 / (8 * (Real.log 2 * (p * (1 - p)))) * 2 := by
    rw [hκ, hd]; field_simp; ring
  nlinarith

/-- Normalized double-cap lower bound. -/
theorem dc_lower_normalized {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1 / 2) :
    (q - p) ^ 2 * (1 / (2 * (Real.log 2 * (q * (1 - q)))) -
        radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J ((p + q) / 2))) ≤
      canonicalPureGap p q (H p) (H q) := by
  have hL := log_two_pos
  have hq0 : 0 < q := hp.trans hpq
  have hpp : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hqq : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have hdc := dc_lower_w hp hpq hq.le
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
  -- interiorCost lower bound
  have hj : (q - p) ^ 2 / (2 * (Real.log 2 * (q * (1 - q)))) ≤ interiorCost p q := by
    have h := J_sub_ge hp hpq.le hq.le
    unfold interiorCost
    have hqp : 0 ≤ q - p := by linarith
    have := mul_le_mul_of_nonneg_left h hqp
    have hX : 0 < Real.log 2 * (q * (1 - q)) := by positivity
    have e : (q - p) ^ 2 / (2 * (Real.log 2 * (q * (1 - q)))) =
        (q - p) * ((q - p) / (Real.log 2 * (q * (1 - q)))) / 2 := by
      field_simp
    rw [e]
    linarith
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
  have e3 : (q - p) ^ 2 * (1 / (2 * (Real.log 2 * (q * (1 - q)))) -
      radialSlope p / (4 * (Real.log 2 * (p * (1 - p))) * J m)) =
      (q - p) ^ 2 / (2 * (Real.log 2 * (q * (1 - q)))) -
        (q - p) ^ 2 / (4 * (Real.log 2 * (p * (1 - p))) * J m) * radialSlope p := by ring
  rw [e3]
  linarith

end CKLaneP

end


