-- Prove2me | Definitions.Def_CK_CKLaneN1c_NormAnalytic
-- name    : CK_CKLaneN1c_NormAnalytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:36:11.780082+00:00
-- url     : https://prove2.me/theorems/f68a7fd5-299d-45a9-96a4-6baa20070d6b
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.NormAnalytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.NormAnalytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.NormAnalytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.NormAnalytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/NormAnalytic.lean)

import Definitions.Def_CK_CKLaneN1_Analytic
import Definitions.Def_CK_CKLaneD_Analytic
import Definitions.Def_CK_GeneralCK_PsiLowEntropyRedesign
import Definitions.Def_CK_GeneralCK_PhiEntropyConvexity
import Definitions.Def_CK_GeneralCK_RadialConcavity
import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Definitions.Def_CK_CKLaneN1c_EndpointGain

-- ===== source module CKLaneN1c.NormAnalytic =====
section

/-!
# Lane N1c-c: analytic lemmas of the `normalized_phi_children` owner (transition PROOF.md §3)

* `neg_deriv_eta_sub_two_ge`, `eta_increment_ge_of_slope`, `parent_gain_box` — the retained logarithmic
  slope inequality with the archived constant
  `β = (1-2v₊)/(L(1-v₊)) · (1 + 1/log((1-v₋)/v₋))` and the normalized parent bound (9);
* `child_tangent`, `childAverage_lower` — entropy convexity of `Φ(z,·) = η - F(z,·)` with the archived
  compensation `γ = max(0, 1/(2L) - (13/6)s)` (6): via the corpus quantitative tangent
  (`radialPhi_tangent_lower`, compensation `1/L - 13z/6 ≥ γ`) when `γ > 0`, and via feasible-fiber
  convexity (`radialPhi_entropy_convexOn`) when `γ = 0`;
* `radialSlope_antitoneOn`, `radial_ratio_le_slope`, `radialSlope_le`, `radialLoss_le` — radial concavity
  (8) with `W(x) = f'(x)/(2x)` bounded at a lower contact bracket;
* `split_loss` — minimizing `c τ² - (13q/6)|τ|` gives the loss `169 q²/(144 c)` (7).

Everything is proved from GeneralCK corpus theorems and Mathlib; no numerical input.
-/

set_option autoImplicit false

namespace CKLaneN1c.NA

open GeneralCK Set PsiChildEntropyCoupling PsiSignedSplit PsiExtendedEntropyCurvature

/-! ## Parent entropy gain -/

/-- `h(-η'(h) - 2) ≥ (1-2v)/(L(1-v)) · (1 + 1/log((1-v)/v))`, `v = H⁻¹(h)`. -/
theorem neg_deriv_eta_sub_two_ge {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    (1 - 2 * entropyInverse h) / (Real.log 2 * (1 - entropyInverse h)) *
      (1 + 1 / Real.log ((1 - entropyInverse h) / entropyInverse h)) ≤
      h * (-deriv eta h - 2) := by
  have hv : 0 < entropyInverse h := entropyInverse_pos h0 h1.le
  have hv' : entropyInverse h < 1 / 2 := entropyInverse_lt_half h0.le h1
  have hH : H (entropyInverse h) = h := (entropyInverse_spec h0.le h1.le).2.2
  rw [deriv_eta h0 h1]
  set v := entropyInverse h with hv_def
  set l := Real.log ((1 - v) / v) with hl_def
  have hlpos : 0 < l := CKLaneN1.logit_pos hv hv'
  have hL : 0 < Real.log 2 := log_two_pos
  have hv1 : 0 < 1 - v := by linarith
  have hJ : J v = l / Real.log 2 := rfl
  have hden : Real.log 2 * v * (1 - v) * J v = v * (1 - v) * l := by
    rw [hJ]; field_simp
  have hn := PsiExtendedEntropyCurvature.entropy_natural_lower hv (by linarith : v < 1)
  rw [hH] at hn
  rw [hden]
  have hsimp : h * (-(-2 - (1 - 2 * v) / (v * (1 - v) * l)) - 2) =
      (1 - 2 * v) / (Real.log 2 * (1 - v)) * ((h * Real.log 2 / v) / l) := by
    field_simp
    ring
  rw [hsimp]
  have hA : 0 ≤ (1 - 2 * v) / (Real.log 2 * (1 - v)) := by
    apply div_nonneg (by linarith) (by positivity)
  apply mul_le_mul_of_nonneg_left _ hA
  have e2 : 1 + 1 / l = (l + 1) / l := by field_simp
  rw [e2]
  apply div_le_div_of_nonneg_right _ hlpos.le
  rw [le_div_iff₀ hv]
  linarith

/-- Integrated slope bound: `2(y'-y) + K (log y' - log y) ≤ η(y) - η(y')`. -/
theorem eta_increment_ge_of_slope {y y' K : ℝ} (hy : 0 < y) (hyy : y ≤ y') (hy1 : y' < 1)
    (hK : ∀ h ∈ Icc y y', K ≤ h * (-deriv eta h - 2)) :
    2 * (y' - y) + K * (Real.log y' - Real.log y) ≤ eta y - eta y' := by
  have hanti : AntitoneOn (fun h => eta h + 2 * h + K * Real.log h) (Icc y y') := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc y y')
      (f' := fun h => deriv eta h + 2 + K / h)
    · intro h hh
      have h0 : 0 < h := hy.trans_le hh.1
      have h1 : h < 1 := lt_of_le_of_lt hh.2 hy1
      exact (((hasDerivAt_eta h0 h1).continuousAt.add
        (continuousAt_const.mul continuousAt_id)).add
        (continuousAt_const.mul (Real.continuousAt_log h0.ne'))).continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have h0 : 0 < h := hy.trans hh.1
      have h1 : h < 1 := lt_trans hh.2 hy1
      have e1 : HasDerivAt eta (deriv eta h) h :=
        (hasDerivAt_eta h0 h1).differentiableAt.hasDerivAt
      have e2 : HasDerivAt (fun x : ℝ => 2 * x) 2 h := by
        simpa using (hasDerivAt_id h).const_mul (2 : ℝ)
      have e3 : HasDerivAt (fun x : ℝ => K * Real.log x) (K / h) h := by
        simpa [div_eq_mul_inv] using (Real.hasDerivAt_log h0.ne').const_mul K
      exact ((e1.add e2).add e3).hasDerivWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      have h0 : 0 < h := hy.trans hh.1
      have hk := hK h ⟨hh.1.le, hh.2.le⟩
      have : K / h ≤ -deriv eta h - 2 := by
        rw [div_le_iff₀ h0]
        linarith
      linarith
  have := hanti ⟨le_refl y, hyy⟩ ⟨hyy, le_refl y'⟩ hyy
  simp only at this
  linarith

/-- `C(q) = 1 - H((1-q)/2) ≥ q²/(2L)` (from `SmallMean.Cn_ge_half_sq`). -/
theorem C_ge_half_sq {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    q ^ 2 / (2 * Real.log 2) ≤ 1 - H ((1 - q) / 2) := by
  have h := SmallMean.Cn_ge_half_sq hq hq1
  unfold SmallMean.Cn at h
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
  nlinarith

/-- Transition PROOF.md (9) in product form: for `E ≤ h ≤ E + C` the brackets `v₋ ≤ H⁻¹(h) ≤ v₊`
give the archived slope constant `β`, and `ℓ₀ = log(1+u)/u` is bounded below at `u ≥ C/E`. -/
theorem parent_gain_box {E C q vp vm lhi lu u L1 : ℝ}
    (hE : 0 < E) (hC0 : 0 ≤ C) (hCq : q ^ 2 / (2 * Real.log 2) ≤ C)
    (hEC1 : E + C < 1) (hvp0 : 0 ≤ vp) (hvp : vp < 1 / 2) (hHvp : E + C ≤ H vp)
    (hvm0 : 0 < vm) (hvm : vm ≤ 1 / 2) (hHvm : H vm ≤ E)
    (hlhi : Real.log ((1 - vm) / vm) ≤ lhi) (hL1 : Real.log 2 ≤ L1)
    (hu0 : 0 < u) (hu : C / E ≤ u) (hlu : lu ≤ Real.log (1 + u)) (hlu0 : 0 ≤ lu) :
    q ^ 2 / E * (E / L1 + (1 - 2 * vp) / (L1 * (1 - vp)) * (1 + 1 / lhi) / (2 * L1) * (lu / u)) ≤
      eta E - eta (E + C) := by
  have hL := log_two_pos
  have hL1pos : 0 < L1 := hL.trans_le hL1
  have hvp1 : 0 < 1 - vp := by linarith
  have hvp2 : 0 < 1 - 2 * vp := by linarith
  set β := (1 - 2 * vp) / (L1 * (1 - vp)) * (1 + 1 / lhi) with hβ_def
  -- positivity of `lhi`
  have hlvm : 0 ≤ Real.log ((1 - vm) / vm) := CKLaneN1.logit_nonneg hvm0 hvm
  -- the slope bound on `[E, E + C]`
  have hK : ∀ h ∈ Icc E (E + C), β ≤ h * (-deriv eta h - 2) := by
    intro h hh
    have h0 : 0 < h := hE.trans_le hh.1
    have h1 : h < 1 := lt_of_le_of_lt hh.2 hEC1
    have hv := entropyInverse_pos h0 h1.le
    have hv' := entropyInverse_lt_half h0.le h1
    have hHv : H (entropyInverse h) = h := (entropyInverse_spec h0.le h1.le).2.2
    set v := entropyInverse h with hv_def
    -- `v ≤ vp`
    have hvvp : v ≤ vp := by
      by_contra hn
      have hlt : vp < v := lt_of_not_ge hn
      have := H_strictMonoOn ⟨hvp0, hvp.le⟩ ⟨hv.le, hv'.le⟩ hlt
      linarith [hh.2]
    -- `vm ≤ v`
    have hvmv : vm ≤ v := by
      by_contra hn
      have hlt : v < vm := lt_of_not_ge hn
      have := H_strictMonoOn ⟨hv.le, hv'.le⟩ ⟨hvm0.le, hvm⟩ hlt
      linarith [hh.1]
    have hlv : 0 < Real.log ((1 - v) / v) := CKLaneN1.logit_pos hv hv'
    have hlvle : Real.log ((1 - v) / v) ≤ lhi := by
      refine le_trans ?_ hlhi
      apply Real.log_le_log (div_pos (by linarith) hv)
      rw [div_le_div_iff₀ hv hvm0]
      nlinarith
    have hlhipos : 0 < lhi := hlv.trans_le hlvle
    have hbase := neg_deriv_eta_sub_two_ge h0 h1
    refine le_trans ?_ hbase
    -- compare the two factors
    have hf1 : (1 - 2 * vp) / (L1 * (1 - vp)) ≤ (1 - 2 * v) / (Real.log 2 * (1 - v)) := by
      have hv1 : 0 < 1 - v := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hA : (1 - 2 * vp) * (1 - v) ≤ (1 - 2 * v) * (1 - vp) := by nlinarith
      have hB := mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ (1 - 2 * v) * (1 - vp) by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left hA hL.le]
    have hf2 : 1 + 1 / lhi ≤ 1 + 1 / Real.log ((1 - v) / v) := by
      have := one_div_le_one_div_of_le hlv hlvle
      linarith
    have hf1n : 0 ≤ (1 - 2 * vp) / (L1 * (1 - vp)) := div_nonneg hvp2.le (by positivity)
    have hf2n : 0 ≤ 1 + 1 / lhi := by positivity
    exact mul_le_mul hf1 hf2 hf2n (hf1n.trans hf1)
  have hinc := eta_increment_ge_of_slope hE (by linarith) hEC1 hK
  -- `β ≥ 0`
  have hlhi0 : 0 ≤ lhi := hlvm.trans hlhi
  have hβ0 : 0 ≤ β := by
    rw [hβ_def]
    apply mul_nonneg (div_nonneg hvp2.le (by positivity))
    rcases eq_or_lt_of_le hlhi0 with h0 | h0
    · rw [← h0]; simp
    · positivity
  -- `log(1 + C/E) ≥ (C/E) (lu/u)`
  have hlog : C / E * (lu / u) ≤ Real.log (E + C) - Real.log E := by
    have he : Real.log (E + C) - Real.log E = Real.log (1 + C / E) := by
      rw [← Real.log_div (by linarith) hE.ne']
      congr 1
      field_simp
    rw [he]
    rcases eq_or_lt_of_le hC0 with hc | hc
    · rw [← hc]; simp
    · have hz : 0 < C / E := div_pos hc hE
      have hanti := CKLaneN1.log_one_add_div_anti hz hu
      have h1 : C / E * Real.log (1 + u) ≤ u * Real.log (1 + C / E) := hanti
      have h2 : C / E * lu ≤ C / E * Real.log (1 + u) := mul_le_mul_of_nonneg_left hlu hz.le
      rw [mul_div_assoc', div_le_iff₀ hu0]
      linarith
  have hmain : 2 * C + β * (C / E * (lu / u)) ≤ eta E - eta (E + C) := by
    have := mul_le_mul_of_nonneg_left hlog hβ0
    have e : 2 * (E + C - E) = 2 * C := by ring
    rw [e] at hinc
    linarith
  -- compare with the target
  have hC2 : q ^ 2 / L1 ≤ 2 * C := by
    have h1 : q ^ 2 / L1 ≤ q ^ 2 / Real.log 2 :=
      div_le_div_of_nonneg_left (sq_nonneg q) hL hL1
    have h2 : q ^ 2 / Real.log 2 = 2 * (q ^ 2 / (2 * Real.log 2)) := by field_simp
    linarith
  have hC3 : q ^ 2 / (2 * L1 * E) ≤ C / E := by
    have h1 : q ^ 2 / (2 * L1) ≤ q ^ 2 / (2 * Real.log 2) :=
      div_le_div_of_nonneg_left (sq_nonneg q) (by positivity) (by linarith)
    have h2 : q ^ 2 / (2 * L1 * E) = q ^ 2 / (2 * L1) / E := by rw [div_div]
    rw [h2]
    exact div_le_div_of_nonneg_right (h1.trans hCq) hE.le
  have hlu' : 0 ≤ lu / u := div_nonneg hlu0 hu0.le
  have hC4 : β * (q ^ 2 / (2 * L1 * E) * (lu / u)) ≤ β * (C / E * (lu / u)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC3 hlu') hβ0
  have htarget : q ^ 2 / E * (E / L1 + β / (2 * L1) * (lu / u)) =
      q ^ 2 / L1 + β * (q ^ 2 / (2 * L1 * E) * (lu / u)) := by
    field_simp
  have e3 : (1 - 2 * vp) / (L1 * (1 - vp)) * (1 + 1 / lhi) / (2 * L1) * (lu / u) =
      β / (2 * L1) * (lu / u) := by rw [hβ_def]
  rw [e3, htarget]
  linarith

/-! ## Child tangent lines with compensation `γ` -/

theorem radialPhi_hasDerivAt {z h : ℝ} (hz : 0 ≤ z) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (radialPhi z) (deriv (radialPhi z) h) h := by
  rcases hz.eq_or_lt with he | hp
  · rw [← he, EntropyCurvature.radialPhi_zero]
    exact (hasDerivAt_eta hh hh1).differentiableAt.hasDerivAt
  · exact (EntropyCurvature.hasDerivAt_radialPhi_entropy hp hh hh1).differentiableAt.hasDerivAt

theorem log_ratio_bracket_nonneg {E h : ℝ} (hE : 0 < E) (hh : 0 < h) :
    0 ≤ (h - E) / E - Real.log (h / E) := by
  have := Real.log_le_sub_one_of_pos (div_pos hh hE)
  have e : h / E - 1 = (h - E) / E := by field_simp
  linarith

/-- Supporting line at `E` for one child `Φ(z,·)`, with compensation `γ` (`γ = 0` or
`γ ≤ 1/L - 13z/6`), valid for every child entropy `0 < h ≤ 11/100`. -/
theorem child_tangent {z E h γ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 4 / 5) (hE : 0 < E)
    (hEi : E ≤ 11 / 100) (hh : 0 < h) (hhi : h ≤ 11 / 100)
    (hγ : γ = 0 ∨ γ ≤ compensation z) :
    radialPhi z E + deriv (radialPhi z) E * (h - E) + γ * ((h - E) / E - Real.log (h / E)) ≤
      radialPhi z h := by
  have hbr := log_ratio_bracket_nonneg hE hh
  rcases hγ with h0 | hle
  · -- feasible-fiber convexity
    rw [h0, zero_mul, add_zero]
    have hcap : (11 / 100 : ℝ) ≤ H ((1 - z) / 2) := by
      have h1 := CKLaneD.H_mono_left (show (0 : ℝ) ≤ 1 / 10 by norm_num)
        (show (1 : ℝ) / 10 ≤ (1 - z) / 2 by linarith) (show (1 - z) / 2 ≤ 1 / 2 by linarith)
      linarith [Gain.H_tenth_ge]
    have hc := radialPhi_entropy_convexOn hz (by linarith)
    have hd := radialPhi_hasDerivAt hz hE (by linarith)
    have hEm : E ∈ Ioc 0 (H ((1 - z) / 2)) := ⟨hE, by linarith⟩
    have hhm : h ∈ Ioc 0 (H ((1 - z) / 2)) := ⟨hh, by linarith⟩
    rcases lt_trichotomy E h with hlt | he | hgt
    · have hs := hc.le_slope_of_hasDerivAt hEm hhm hlt hd
      rw [slope_def_field] at hs
      have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
      linarith
    · rw [← he]; simp
    · have hs := hc.slope_le_of_hasDerivAt hhm hEm hgt hd
      rw [slope_def_field] at hs
      have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
      nlinarith
  · -- quantitative tangent of the corpus, compensation `1/L - 13z/6 ≥ γ`
    have ht := radialPhi_tangent_lower hz hE hEi hh hhi
    have := mul_le_mul_of_nonneg_right hle hbr
    linarith

/-- Transition PROOF.md §3: the two supporting lines at `E`, summed over the split `e = E(1+t)`,
`f = E(1-t)`. -/
theorem childAverage_lower {d q E t γ : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d) (hdq : d + q ≤ 4 / 5)
    (hE : 0 < E) (hEi : E ≤ 11 / 200) (ht : |t| < 1)
    (hγ : γ = 0 ∨ γ ≤ compensation (d + q)) :
    (radialPhi (d + q) E + radialPhi (d - q) E) / 2 + E * t * slopeDifference d q E / 2 +
      γ * barrier t / 2 ≤ childAverage d q E t := by
  have hti := abs_lt.mp ht
  have hep : 0 < E * (1 + t) := mul_pos hE (by linarith)
  have hem : 0 < E * (1 - t) := mul_pos hE (by linarith)
  have hEp : E * (1 + t) ≤ 11 / 100 := by
    nlinarith [mul_pos hE (show 0 < 1 - t by linarith)]
  have hEm : E * (1 - t) ≤ 11 / 100 := by
    nlinarith [mul_pos hE (show 0 < 1 + t by linarith)]
  have hγm : γ = 0 ∨ γ ≤ compensation (d - q) := by
    rcases hγ with h0 | hle
    · exact Or.inl h0
    · right
      refine hle.trans ?_
      unfold compensation
      linarith
  have hp := child_tangent (z := d + q) (by linarith) hdq hE (by linarith) hep hEp hγ
  have hm := child_tangent (z := d - q) (by linarith) (by linarith) hE (by linarith) hem hEm hγm
  have hpr : (E * (1 + t) - E) / E = t := by field_simp; ring
  have hmr : (E * (1 - t) - E) / E = -t := by field_simp; ring
  have hpl : E * (1 + t) / E = 1 + t := by field_simp
  have hml : E * (1 - t) / E = 1 - t := by field_simp
  rw [hpr, hpl] at hp
  rw [hmr, hml] at hm
  unfold childAverage slopeDifference barrier
  rw [log_one_sub_sq ht]
  linear_combination hp / 2 + hm / 2

/-! ## Radial concavity and the slope bound -/

theorem log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have h := CKLaneE.FP.log_two_mem.1
  have h2 : (1 / 2 : ℚ) < CKLaneE.FP.LqLo := by decide +kernel
  have h3 : ((1 / 2 : ℚ) : ℝ) < ((CKLaneE.FP.LqLo : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith

theorem radialSlope_antitoneOn : AntitoneOn radialSlope (Ioo 0 (1 / 2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 (1 / 2))
    (f' := fun v => -Certificates.Mixed.hn v * (2 * Certificates.Mixed.kap v - (1 - 2 * v) ^ 2) /
      (4 * Real.log 2 * v ^ 2 * (1 - v) ^ 2 * Certificates.Mixed.kap v ^ 2))
  · intro v hv
    exact (hasDerivAt_radialSlope hv.1 hv.2).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioo] at hv
    exact (hasDerivAt_radialSlope hv.1 hv.2).hasDerivWithinAt
  · intro v hv
    rw [interior_Ioo] at hv
    have hk := kap_ge_log_two hv.1 (by linarith [hv.2])
    have hL := log_two_gt_half
    have hhn : 0 ≤ Certificates.Mixed.hn v := by
      rw [Certificates.Mixed.hn_eq_H_mul_log]
      exact mul_nonneg (H_nonneg hv.1.le (by linarith [hv.2])) log_two_pos.le
    have hsq : (1 - 2 * v) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hnum : 0 ≤ 2 * Certificates.Mixed.kap v - (1 - 2 * v) ^ 2 := by linarith
    apply div_nonpos_of_nonpos_of_nonneg
    · have := mul_nonneg hhn hnum
      linarith
    · have := Certificates.Mixed.kap_pos hv.1 hv.2
      have hv1 : 0 < 1 - v := by linarith [hv.2]
      have := log_two_pos
      positivity

/-- `f'(x)/(2x) ≤ radialSlope(v_l)/(2x₀)` for `x ≥ x₀ > 0` and a lower contact bracket `v_l`. -/
theorem radial_ratio_le_slope {x x0 vl : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x) (hvl0 : 0 < vl)
    (hvl : vl < 1 / 2) (hvlc : x0 * H vl ≤ 1 - 2 * vl) :
    deriv (fun r => F r 1) x / (2 * x) ≤ radialSlope vl / (2 * x0) := by
  have hm := antitoneOn_F_radius_ratio (h := 1) one_pos (show x0 ∈ Ioi (0 : ℝ) from hx0)
    (show x ∈ Ioi (0 : ℝ) from hx0.trans_le hx) hx
  simp only at hm
  refine hm.trans ?_
  rw [deriv_F_radius_slope hx0 one_pos]
  have hrc : vl ≤ radialContact x0 1 := by
    rw [le_radialContact_iff hx0 one_pos hvl0.le hvl.le]
    linarith
  have hrc1 := radialContact_lt_half hx0 one_pos
  have hs : radialSlope (radialContact x0 1) ≤ radialSlope vl :=
    radialSlope_antitoneOn ⟨hvl0, hvl⟩ ⟨hvl0.trans_le hrc, hrc1⟩ hrc
  exact div_le_div_of_nonneg_right hs (by linarith)

/-- Rational upper bound of `radialSlope v` from enclosures of `J`, `hn`, `kap`, `log 2`. -/
theorem radialSlope_le {v Jh hnh kl L0 : ℝ} (hv0 : 0 < v) (hv : v < 1 / 2) (hJ : J v ≤ Jh)
    (hhn : Certificates.Mixed.hn v ≤ hnh) (hkl : 0 < kl) (hk : kl ≤ Certificates.Mixed.kap v)
    (hL0 : 0 < L0) (hL0le : L0 ≤ Real.log 2) :
    radialSlope v ≤ Jh + (1 - 2 * v) * hnh / (2 * L0 * v * (1 - v) * kl) := by
  unfold radialSlope
  have hv1 : 0 < 1 - v := by linarith
  have hr : 0 ≤ 1 - 2 * v := by linarith
  have hhn0 : 0 ≤ Certificates.Mixed.hn v := by
    rw [Certificates.Mixed.hn_eq_H_mul_log]
    exact mul_nonneg (H_nonneg hv0.le (by linarith)) log_two_pos.le
  have hL := log_two_pos
  have hd1 : 0 < 2 * L0 * v * (1 - v) * kl := by positivity
  have hd2 : 2 * L0 * v * (1 - v) * kl ≤ 2 * Real.log 2 * v * (1 - v) * Certificates.Mixed.kap v := by
    have h1 : 2 * L0 * (v * (1 - v)) * kl ≤ 2 * Real.log 2 * (v * (1 - v)) * kl := by
      have := mul_le_mul_of_nonneg_right hL0le (show 0 ≤ 2 * (v * (1 - v)) * kl by positivity)
      nlinarith
    have h2 : 2 * Real.log 2 * (v * (1 - v)) * kl ≤
        2 * Real.log 2 * (v * (1 - v)) * Certificates.Mixed.kap v :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    nlinarith
  have hnum : (1 - 2 * v) * Certificates.Mixed.hn v ≤ (1 - 2 * v) * hnh :=
    mul_le_mul_of_nonneg_left hhn hr
  have hfrac : (1 - 2 * v) * Certificates.Mixed.hn v /
      (2 * Real.log 2 * v * (1 - v) * Certificates.Mixed.kap v) ≤
      (1 - 2 * v) * hnh / (2 * L0 * v * (1 - v) * kl) := by
    calc (1 - 2 * v) * Certificates.Mixed.hn v /
          (2 * Real.log 2 * v * (1 - v) * Certificates.Mixed.kap v)
        ≤ (1 - 2 * v) * Certificates.Mixed.hn v / (2 * L0 * v * (1 - v) * kl) :=
          div_le_div_of_nonneg_left (mul_nonneg hr hhn0) hd1 hd2
      _ ≤ (1 - 2 * v) * hnh / (2 * L0 * v * (1 - v) * kl) :=
          div_le_div_of_nonneg_right hnum hd1.le
  linarith

/-- Transition PROOF.md (8): `(F(d+q,E)+F(d-q,E))/2 - F(d,E) ≤ (q²/E) · f'(x)/(2x)`, `x = d/E`. -/
theorem radialLoss_le {d q E : ℝ} (hd : 0 < d) (hE : 0 < E) (hq : 0 ≤ q) (hqd : q ≤ d) :
    radialLoss d q E ≤ q ^ 2 / E * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
  have hh := F_average_difference_le hd hE q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith), abs_of_nonneg (show 0 ≤ d + q by linarith)] at hh
  have heq : q ^ 2 / (2 * d) * deriv (fun r => F r E) d =
      q ^ 2 / E * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd hE]
    field_simp
  unfold radialLoss
  linarith

/-! ## The split loss -/

theorem barrier_ge_sq {t : ℝ} (ht : |t| < 1) : t ^ 2 ≤ barrier t := by
  have hh := abs_lt.mp ht
  have hp : 0 < 1 - t ^ 2 := by nlinarith
  have := Real.log_le_sub_one_of_pos hp
  unfold barrier
  linarith

/-- Transition PROOF.md (7): `E t A/2 + c 𝒥(t) ≥ -169 q²/(144 c)` for `0 ≤ A ≤ 13q/(3E)`. -/
theorem split_loss {c A E q t : ℝ} (hc : 0 < c) (hE : 0 < E) (hA0 : 0 ≤ A)
    (hA : A ≤ 13 * q / (3 * E)) (ht : |t| < 1) :
    -(169 * q ^ 2 / (144 * c)) ≤ E * t * A / 2 + c * barrier t := by
  have hb := barrier_ge_sq ht
  set s := |t| with hs
  have hs0 : 0 ≤ s := abs_nonneg t
  have hts : -s ≤ t := neg_abs_le t
  have ht2 : t ^ 2 = s ^ 2 := (sq_abs t).symm
  have hEA : E * A ≤ 13 * q / 3 := by
    have := mul_le_mul_of_nonneg_left hA hE.le
    have e : E * (13 * q / (3 * E)) = 13 * q / 3 := by field_simp
    linarith
  have h1 : -(s * (13 * q / 3)) / 2 ≤ E * t * A / 2 := by
    have hEA0 : 0 ≤ E * A := mul_nonneg hE.le hA0
    have := mul_le_mul_of_nonneg_left hts hEA0
    have h2 : s * (E * A) ≤ s * (13 * q / 3) := mul_le_mul_of_nonneg_left hEA hs0
    nlinarith
  have h3 : c * s ^ 2 ≤ c * barrier t := by
    rw [← ht2]; exact mul_le_mul_of_nonneg_left hb hc.le
  have hsq : 0 ≤ (12 * c * s - 13 * q) ^ 2 / (144 * c) := by positivity
  have hid : (12 * c * s - 13 * q) ^ 2 / (144 * c) =
      c * s ^ 2 - 13 * q / 6 * s + 169 * q ^ 2 / (144 * c) := by
    field_simp
    ring
  nlinarith

end CKLaneN1c.NA

end


