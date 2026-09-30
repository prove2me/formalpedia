-- Prove2me | Definitions.Def_CK_CKLaneN1_EdgeAlg
-- name    : CK_CKLaneN1_EdgeAlg
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:44:32.662624+00:00
-- url     : https://prove2.me/theorems/1b801f2e-81ed-4ce0-832c-1050f715bbde
-- title:
--   Courtade–Kumar proof module `CKLaneN1.EdgeAlg` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.EdgeAlg` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.EdgeAlg` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.EdgeAlg (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/EdgeAlg.lean)

import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_PureGapMiddleDeterministic
import Definitions.Def_CK_GeneralCK_EntropyComparison
import Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff

-- ===== source module CKLaneN1.EdgeAlg =====
section

set_option autoImplicit false

/-!
# Lane N1: leftEdge — exact radial form and analytic lower bounds

For `0 < a < b < c := S - a ≤ 1/2`, with `h = (H a + H b)/2`, `q = entropyInverse h`:

`cPG a c (H a) (H b) = F (c-a) h + interiorCost a b - F (b-a) h
    - (F (1-2q) h - F (1-S) h) + (F (1-2b) (H b) - F (1-2c) (H b)) / 2`.

Lower bounds used by the box certificate (`Θ = e8Theta`):
* `F y h - F d h ≥ (Θ X / X) (y² - d²) / (4h)` for `X ≥ y/(2h)` (ratio `Θ(x)/x` antitone);
* tangent lines of the convex `r ↦ F r h` (slope `Θ (r/(2h))`);
* `a ≤ q ≤ M = (a+b)/2` and `J M (M - q) ≤ H M - h`.
-/

namespace CKLaneN1.Edge

open GeneralCK Set

/-! ## Cap evaluations -/

theorem F_cap {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : F (1 - 2 * v) (H v) = (1 - 2 * v) * J v := by
  have hne : (1 - 2 * v) ≠ 0 := by linarith
  simp only [F, hne, if_false, radialContact_H_lower hv hv']

theorem eta_eq_F_cap {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    eta h = F (1 - 2 * entropyInverse h) h := by
  obtain ⟨-, -, hH⟩ := entropyInverse_spec h0.le h1.le
  have hq0 : 0 < entropyInverse h := entropyInverse_pos h0 h1.le
  have hq1 : entropyInverse h < 1 / 2 := entropyInverse_lt_half h0.le h1
  have hne : h ≠ 1 := ne_of_lt h1
  have hF := F_cap hq0 hq1
  rw [hH] at hF
  rw [hF]
  simp only [eta, hne, if_false]

theorem H_lt_one {v : ℝ} (hv : 0 ≤ v) (hv' : v < 1 / 2) : H v < 1 := by
  have h := H_strictMonoOn ⟨hv, hv'.le⟩ ⟨by norm_num, le_rfl⟩ hv'
  have hh : H (1 / 2 : ℝ) = 1 := by
    simp [H, Real.binEntropy]
    have : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, Real.log_inv]
    have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
    ring
  linarith

theorem H_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : H u ≤ H v :=
  H_strictMonoOn.monotoneOn ⟨hu, huv.trans hv⟩ ⟨hu.trans huv, hv⟩ huv

/-! ## Exact radial form of the cutoff-edge value -/

/-- The cutoff-edge value in explicit radial differences. -/
theorem cpg_edge_eq {S a b : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < S - a)
    (hc : S - a ≤ 1 / 2) :
    canonicalPureGap a (S - a) (H a) (H b) =
      F (S - 2 * a) ((H a + H b) / 2) + interiorCost a b - F (b - a) ((H a + H b) / 2) -
        (F (1 - 2 * entropyInverse ((H a + H b) / 2)) ((H a + H b) / 2) -
          F (1 - S) ((H a + H b) / 2)) +
        (F (1 - 2 * b) (H b) - F (1 - 2 * (S - a)) (H b)) / 2 := by
  have hb2 : b < 1 / 2 := by linarith
  have ha2 : a < 1 / 2 := by linarith
  have hHa : 0 < H a := H_pos ha (by linarith)
  have hHb1 : H b < 1 := H_lt_one (by linarith) hb2
  have hHa1 : H a < 1 := H_lt_one ha.le ha2
  have hh0 : 0 < (H a + H b) / 2 := by
    have := H_nonneg (show (0 : ℝ) ≤ b by linarith) (by linarith); linarith
  have hh1 : (H a + H b) / 2 < 1 := by linarith
  have hia : entropyInverse (H a) = a := entropyInverse_H_lower ha.le ha2.le
  have hib : entropyInverse (H b) = b := entropyInverse_H_lower (by linarith) hb2.le
  have habs : |a - b| = b - a := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
  have hcapa : radialPhi (1 - 2 * a) (H a) = 0 := by
    unfold radialPhi
    rw [Comparison.eta_H ha ha2, F_cap ha ha2]
    ring
  have hcapb : eta (H b) = F (1 - 2 * b) (H b) := by
    rw [Comparison.eta_H (by linarith) hb2, F_cap (by linarith) hb2]
  have heta : eta ((H a + H b) / 2) =
      F (1 - 2 * entropyInverse ((H a + H b) / 2)) ((H a + H b) / 2) := eta_eq_F_cap hh0 hh1
  unfold canonicalPureGap entropyCorrection atomCorrection
  rw [hia, hib, habs, hcapa]
  unfold radialPhi
  rw [heta, hcapb]
  have e1 : S - a - a = S - 2 * a := by ring
  have e2 : 1 - a - (S - a) = 1 - S := by ring
  rw [e1, e2]
  ring

/-! ## Radial lower bounds -/

theorem hasDerivAt_F_theta {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h) (e8Theta (z / (2 * h))) z := by
  have hd := (hasDerivAt_F_radius hz hh).differentiableAt.hasDerivAt
  rwa [deriv_F_radius_eq_e8Theta hz hh] at hd

/-- Ratio bound: `F y h - F d h ≥ (Θ X / X) (y² - d²) / (4h)` whenever `X ≥ y/(2h)`. -/
theorem F_sub_ge_ratio {h d y X : ℝ} (hh : 0 < h) (hd : 0 < d) (hdy : d ≤ y)
    (hX : y / (2 * h) ≤ X) :
    e8Theta X / X * (y ^ 2 - d ^ 2) / (4 * h) ≤ F y h - F d h := by
  have hXpos : 0 < X := lt_of_lt_of_le (div_pos (hd.trans_le hdy) (by linarith)) hX
  have hh' : h ≠ 0 := hh.ne'
  set κ := e8Theta X / X with hκ
  have hg : ∀ r, 0 < r → HasDerivAt (fun r => F r h - κ * r ^ 2 / (4 * h))
      (e8Theta (r / (2 * h)) - κ * r / (2 * h)) r := by
    intro r hr
    have h1 := hasDerivAt_F_theta hr hh
    have h2 : HasDerivAt (fun r => κ * r ^ 2 / (4 * h)) (κ * (2 * r) / (4 * h)) r := by
      have := ((hasDerivAt_pow 2 r).const_mul κ).div_const (4 * h)
      simpa using this
    have h3 := h1.sub h2
    refine (h3.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn (fun r => F r h - κ * r ^ 2 / (4 * h)) (Icc d y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc d y)
    · intro r hr
      exact (hg r (hd.trans_le hr.1)).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact (hg r (hd.trans hr.1)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 : 0 < r := hd.trans hr.1
      rw [(hg r hr0).deriv]
      have hx0 : 0 < r / (2 * h) := div_pos hr0 (by linarith)
      have hxX : r / (2 * h) ≤ X :=
        le_trans (div_le_div_of_nonneg_right hr.2.le (by linarith)) hX
      have hanti := antitoneOn_e8Theta_div (mem_Ioi.mpr hx0) (mem_Ioi.mpr hXpos) hxX
      simp only at hanti
      rw [le_div_iff₀ hx0] at hanti
      have e : κ * r / (2 * h) = κ * (r / (2 * h)) := by ring
      rw [e]
      linarith
  have hm := hmono ⟨le_rfl, hdy⟩ ⟨hdy, le_rfl⟩ hdy
  simp only at hm
  have e : κ * (y ^ 2 - d ^ 2) / (4 * h) = κ * y ^ 2 / (4 * h) - κ * d ^ 2 / (4 * h) := by ring
  rw [e]
  linarith

/-- Tangent line of the convex radial profile. -/
theorem F_tangent {h x0 x : ℝ} (hh : 0 < h) (hx0 : 0 < x0) (hx : 0 ≤ x) :
    F x0 h + e8Theta (x0 / (2 * h)) * (x - x0) ≤ F x h := by
  have hconv := convexOn_F_radius hh
  have hdiff : DifferentiableAt ℝ (fun r => F r h) x0 :=
    (hasDerivAt_F_theta hx0 hh).differentiableAt
  have hder : deriv (fun r => F r h) x0 = e8Theta (x0 / (2 * h)) :=
    deriv_F_radius_eq_e8Theta hx0 hh
  rcases lt_trichotomy x x0 with hlt | heq | hgt
  · have hs := hconv.slope_le_deriv (mem_Ici.mpr hx) (mem_Ici.mpr hx0.le) hlt hdiff
    rw [hder, slope_def_field] at hs
    have hpos : 0 < x0 - x := by linarith
    rw [div_le_iff₀ hpos] at hs
    nlinarith
  · subst heq
    simp
  · have hs := hconv.deriv_le_slope (mem_Ici.mpr hx0.le) (mem_Ici.mpr hx) hgt hdiff
    rw [hder, slope_def_field] at hs
    have hpos : 0 < x - x0 := by linarith
    rw [le_div_iff₀ hpos] at hs
    nlinarith

/-! ## The entropy midpoint inverse `q` -/

theorem J_anti {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) : J v ≤ J u := by
  unfold J
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply Real.log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) hu]
  nlinarith

theorem H_sub_ge_J {q M : ℝ} (hq : 0 < q) (hqM : q ≤ M) (hM : M < 1) :
    J M * (M - q) ≤ H M - H q := by
  have hd : ∀ x, 0 < x → x < 1 → HasDerivAt (fun x => H x - J M * x) (J x - J M) x := by
    intro x hx hx1
    have h1 := (Comparison.hasDerivAt_H hx hx1).sub ((hasDerivAt_id x).const_mul (J M))
    refine (h1.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    ring
  have hmono : MonotoneOn (fun x => H x - J M * x) (Icc q M) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc q M)
    · intro x hx
      exact (hd x (hq.trans_le hx.1) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (hq.trans hx.1) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (hq.trans hx.1) (by linarith [hx.2])).deriv]
      have := J_anti (hq.trans hx.1) hx.2.le hM
      linarith
  have hm := hmono ⟨le_rfl, hqM⟩ ⟨hqM, le_rfl⟩ hqM
  simp only at hm
  nlinarith

theorem q_facts {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) :
    a ≤ entropyInverse ((H a + H b) / 2) ∧
    entropyInverse ((H a + H b) / 2) ≤ (a + b) / 2 ∧
    J ((a + b) / 2) * ((a + b) / 2 - entropyInverse ((H a + H b) / 2)) ≤
      H ((a + b) / 2) - (H a + H b) / 2 ∧
    H (entropyInverse ((H a + H b) / 2)) = (H a + H b) / 2 := by
  have hHab : H a ≤ H b := H_mono ha.le hab hb.le
  have hHa0 : 0 ≤ H a := H_nonneg ha.le (by linarith)
  have hh1 : (H a + H b) / 2 ≤ 1 := by linarith [H_le_one a, H_le_one b]
  have hh0 : 0 ≤ (H a + H b) / 2 := by linarith
  obtain ⟨hq0, hq2, hqH⟩ := entropyInverse_spec hh0 hh1
  have h1 : a ≤ entropyInverse ((H a + H b) / 2) := by
    have := entropyInverse_mono hHa0 hh1 (by linarith : H a ≤ (H a + H b) / 2)
    rwa [entropyInverse_H_lower ha.le (by linarith)] at this
  have hmid := entropy_average_le_midpoint (a := a) (b := b) ha.le (by linarith) (by linarith)
    (by linarith)
  have hM2 : (a + b) / 2 ≤ 1 / 2 := by linarith
  have hM0 : 0 ≤ (a + b) / 2 := by linarith
  have h2 : entropyInverse ((H a + H b) / 2) ≤ (a + b) / 2 := by
    have := entropyInverse_mono hh0 (H_le_one _) hmid
    rwa [entropyInverse_H_lower hM0 hM2] at this
  refine ⟨h1, h2, ?_, hqH⟩
  have := H_sub_ge_J (ha.trans_le h1) h2 (by linarith)
  rwa [hqH] at this

/-! ## Entropy Jensen gap -/

/-- `C r = (1+r) log(1+r) + (1-r) log(1-r)`. -/
noncomputable def Cfun (r : ℝ) : ℝ := (1 + r) * Real.log (1 + r) + (1 - r) * Real.log (1 - r)

theorem negMulLog_pair {M r : ℝ} (hM : 0 < M) (hr0 : -1 < r) (hr1 : r < 1) :
    Real.negMulLog (M * (1 - r)) + Real.negMulLog (M * (1 + r)) =
      2 * Real.negMulLog M - M * Cfun r := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have h2 : (0 : ℝ) < 1 + r := by linarith
  simp only [Real.negMulLog, Cfun]
  rw [Real.log_mul hM.ne' h1.ne', Real.log_mul hM.ne' h2.ne']
  try ring

theorem aux_lin {L P Q R : ℝ} (hL : L ≠ 0) :
    2 * L * (P / L - (Q / L + R / L) / 2) = 2 * P - (Q + R) := by
  field_simp
  try ring

/-- Exact entropy Jensen gap. -/
theorem JH_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 =
      ((a + b) / 2 * Cfun ((b - a) / (a + b)) +
        (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2)))) / (2 * Real.log 2) := by
  have hs : 0 < a + b := by linarith
  have hs' : a + b ≠ 0 := hs.ne'
  have hM1 : 0 < 1 - (a + b) / 2 := by linarith
  have hM1' : 2 * (1 - (a + b) / 2) ≠ 0 := by linarith
  have hL : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hr0 : -1 < (b - a) / (a + b) := by
    rw [lt_div_iff₀ hs]; linarith
  have hr1 : (b - a) / (a + b) < 1 := by
    rw [div_lt_iff₀ hs]; linarith
  have hr0' : -1 < (b - a) / (2 * (1 - (a + b) / 2)) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hr1' : (b - a) / (2 * (1 - (a + b) / 2)) < 1 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  have hA := negMulLog_pair (show 0 < (a + b) / 2 by linarith) hr0 hr1
  have hB := negMulLog_pair hM1 hr0' hr1'
  have ea : (a + b) / 2 * (1 - (b - a) / (a + b)) = a := by field_simp; ring
  have eb : (a + b) / 2 * (1 + (b - a) / (a + b)) = b := by field_simp; ring
  have hN : (1 - (a + b) / 2) ≠ 0 := hM1.ne'
  have h2ab : (2 : ℝ) - (a + b) ≠ 0 := by linarith
  have ea' : (1 - (a + b) / 2) * (1 + (b - a) / (2 * (1 - (a + b) / 2))) = 1 - a := by
    rw [mul_add, mul_one, show (1 - (a + b) / 2) * ((b - a) / (2 * (1 - (a + b) / 2))) =
      (b - a) / 2 by field_simp]
    ring
  have eb' : (1 - (a + b) / 2) * (1 - (b - a) / (2 * (1 - (a + b) / 2))) = 1 - b := by
    rw [mul_sub, mul_one, show (1 - (a + b) / 2) * ((b - a) / (2 * (1 - (a + b) / 2))) =
      (b - a) / 2 by field_simp]
    ring
  rw [ea, eb] at hA
  rw [ea', eb'] at hB
  have hH : ∀ x : ℝ, H x = (Real.negMulLog x + Real.negMulLog (1 - x)) / Real.log 2 := by
    intro x; unfold H; rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [eq_div_iff (mul_ne_zero two_ne_zero hL)]
  rw [show (H ((a + b) / 2) - (H a + H b) / 2) * (2 * Real.log 2) =
      2 * Real.log 2 * (H ((a + b) / 2) - (H a + H b) / 2) by ring]
  rw [hH ((a + b) / 2), hH a, hH b, aux_lin hL]
  linear_combination (-1 : ℝ) * hA + (-1 : ℝ) * hB

/-- `C r ≤ 2 log 2` on `[0, 1]`. -/
theorem Cfun_le_two_log_two {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Cfun r ≤ 2 * Real.log 2 := by
  unfold Cfun
  have h1 : Real.log (1 + r) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  have h2 : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  have h3 : (1 - r) * Real.log (1 - r) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (Real.log_nonpos (by linarith) (by linarith))
  nlinarith

theorem hasDerivAt_log_one_add {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
  have h := ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
  refine (h.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
  simp

theorem hasDerivAt_log_one_sub {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y => Real.log (1 - y)) (-(1 / (1 - x))) x := by
  have h := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
  refine (h.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
  simp [neg_div]

theorem hasDerivAt_Cfun {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt Cfun (Real.log (1 + x) - Real.log (1 - x)) x := by
  have h1 : (1 + x) ≠ 0 := by linarith
  have h2 : (1 - x) ≠ 0 := by linarith
  have ha : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add (1 : ℝ)
  have hb : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  have hC := (ha.mul (hasDerivAt_log_one_add hx0)).add (hb.mul (hasDerivAt_log_one_sub hx1))
  refine (hC.congr_of_eventuallyEq (by filter_upwards with u; simp [Cfun])).congr_deriv ?_
  field_simp
  ring

/-- `E r = 2r/(1-r²) - log((1+r)/(1-r)) ≥ 0` on `[0,1)`. -/
theorem Efun_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ 2 * r / (1 - r ^ 2) - (Real.log (1 + r) - Real.log (1 - r)) := by
  have hd : ∀ x, -1 < x → x < 1 → HasDerivAt
      (fun x => 2 * x / (1 - x ^ 2) - (Real.log (1 + x) - Real.log (1 - x)))
      (4 * x ^ 2 / (1 - x ^ 2) ^ 2) x := by
    intro x hx0 hx1
    have hq : (1 - x ^ 2) ≠ 0 := by nlinarith
    have h1 : (1 + x) ≠ 0 := by linarith
    have h2 : (1 - x) ≠ 0 := by linarith
    have hn : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have hden : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub (1 : ℝ)
    have hE := (hn.div hden hq).sub ((hasDerivAt_log_one_add hx0).sub (hasDerivAt_log_one_sub hx1))
    refine (hE.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn
      (fun x => 2 * x / (1 - x ^ 2) - (Real.log (1 + x) - Real.log (1 - x))) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · intro x hx
      exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      positivity
  have hm := hmono ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  simp only at hm
  norm_num at hm
  linarith

/-- `D r = r log((1+r)/(1-r)) - 2 C r ≥ 0` on `[0,1)`. -/
theorem Dfun_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ r * (Real.log (1 + r) - Real.log (1 - r)) - 2 * Cfun r := by
  have hd : ∀ x, -1 < x → x < 1 → HasDerivAt
      (fun x => x * (Real.log (1 + x) - Real.log (1 - x)) - 2 * Cfun x)
      (2 * x / (1 - x ^ 2) - (Real.log (1 + x) - Real.log (1 - x))) x := by
    intro x hx0 hx1
    have hq : (1 - x ^ 2) ≠ 0 := by nlinarith
    have h1 : (1 + x) ≠ 0 := by linarith
    have h2 : (1 - x) ≠ 0 := by linarith
    have hD := ((hasDerivAt_id x).mul ((hasDerivAt_log_one_add hx0).sub
      (hasDerivAt_log_one_sub hx1))).sub ((hasDerivAt_Cfun hx0 hx1).const_mul 2)
    refine (hD.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    simp only [Pi.sub_apply, id]
    field_simp
    ring
  have hmono : MonotoneOn
      (fun x => x * (Real.log (1 + x) - Real.log (1 - x)) - 2 * Cfun x) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · intro x hx
      exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (by linarith [hx.1]) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact Efun_nonneg hx.1.le (by linarith [hx.2])
  have hm := hmono ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
  simp only [Cfun] at hm
  norm_num at hm
  simp only [Cfun]
  linarith

/-- `C r / r²` is nondecreasing on `(0, 1)`. -/
theorem Chat_mono {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs : s < 1) :
    Cfun r * s ^ 2 ≤ Cfun s * r ^ 2 := by
  have hd : ∀ x, 0 < x → x < 1 → HasDerivAt (fun x => Cfun x / x ^ 2)
      ((x * (Real.log (1 + x) - Real.log (1 - x)) - 2 * Cfun x) / x ^ 3) x := by
    intro x hx0 hx1
    have hx' : x ≠ 0 := hx0.ne'
    have hC := hasDerivAt_Cfun (by linarith) hx1
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hq := hC.div hp (by positivity)
    refine (hq.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    field_simp
    try ring
  have hmono : MonotoneOn (fun x => Cfun x / x ^ 2) (Icc r s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc r s)
    · intro x hx
      exact (hd x (hr.trans_le hx.1) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (hr.trans hx.1) (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (hr.trans hx.1) (by linarith [hx.2])).deriv]
      have hx0 : 0 < x := hr.trans hx.1
      exact div_nonneg (Dfun_nonneg hx0.le (by linarith [hx.2])) (by positivity)
  have hm := hmono ⟨le_rfl, hrs⟩ ⟨hrs, le_rfl⟩ hrs
  simp only at hm
  have hs0 : 0 < s := hr.trans_le hrs
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hm
  linarith

/-! ## Interior cost -/

theorem log_ge_two_mul {x : ℝ} (hx : 1 ≤ x) : 2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have hd : ∀ t, 0 < t → HasDerivAt (fun t => Real.log t - 2 * (t - 1) / (t + 1))
      (1 / t - 4 / (t + 1) ^ 2) t := by
    intro t ht
    have h1 : (t + 1) ≠ 0 := by linarith
    have ht' : t ≠ 0 := ht.ne'
    have hn : HasDerivAt (fun y : ℝ => 2 * (y - 1)) 2 t := by
      simpa using ((hasDerivAt_id t).sub_const (1 : ℝ)).const_mul (2 : ℝ)
    have hden : HasDerivAt (fun y : ℝ => y + 1) 1 t := by
      simpa using (hasDerivAt_id t).add_const (1 : ℝ)
    have hq := (Real.hasDerivAt_log ht.ne').sub (hn.div hden h1)
    refine (hq.congr_of_eventuallyEq (by filter_upwards with u; simp)).congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn (fun t => Real.log t - 2 * (t - 1) / (t + 1)) (Icc 1 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 x)
    · intro t ht
      exact (hd t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t (by linarith [ht.1])).deriv]
      have ht0 : 0 < t := by linarith [ht.1]
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) ht0]
      nlinarith [sq_nonneg (t - 1)]
  have hm := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simp only at hm
  norm_num at hm
  linarith

theorem interiorCost_ge {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    (b - a) ^ 2 / ((a + b) * Real.log 2) ≤ interiorCost a b := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : 0 < a + b := by linarith
  have hs' : a + b ≠ 0 := hs.ne'
  have hs'' : b + a ≠ 0 := by linarith
  have ha' : a ≠ 0 := ha.ne'
  have hsplit : Real.log ((1 - a) / a) - Real.log ((1 - b) / b) =
      Real.log (b / a) + Real.log ((1 - a) / (1 - b)) := by
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) (by linarith),
      Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) (by linarith)]
    ring
  have h1 : 0 ≤ Real.log ((1 - a) / (1 - b)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have h2 := log_ge_two_mul (show 1 ≤ b / a by rw [le_div_iff₀ ha]; linarith)
  have e : 2 * (b / a - 1) / (b / a + 1) = 2 * (b - a) / (a + b) := by
    rw [div_sub_one ha', div_add_one ha']
    field_simp
    ring
  rw [e, div_le_iff₀ hs] at h2
  have hJ : 2 * (b - a) / ((a + b) * Real.log 2) ≤ J a - J b := by
    unfold J
    rw [← sub_div, hsplit, div_le_div_iff₀ (by positivity) hL]
    nlinarith [mul_le_mul_of_nonneg_right h2 hL.le, mul_nonneg h1 (mul_nonneg hs.le hL.le)]
  unfold interiorCost
  have hba : 0 ≤ b - a := by linarith
  have := mul_le_mul_of_nonneg_left hJ hba
  have e2 : (b - a) * (2 * (b - a) / ((a + b) * Real.log 2)) / 2 =
      (b - a) ^ 2 / ((a + b) * Real.log 2) := by
    field_simp
    try ring
  nlinarith

end CKLaneN1.Edge

end


