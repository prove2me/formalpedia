-- Prove2me | Definitions.Def_CK_CKLaneN1_Analytic
-- name    : CK_CKLaneN1_Analytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:54:46.8591+00:00
-- url     : https://prove2.me/theorems/3b46cc89-c927-472b-af2c-2fa151799023
-- title:
--   Courtade–Kumar proof module `CKLaneN1.Analytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.Analytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.Analytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.Analytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/Analytic.lean)

import Definitions.Def_CK_GeneralCK_ProfileDerivatives
import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_RadialConcavity
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_EqualMean

-- ===== source module CKLaneN1.Analytic =====
section

/-!
# Lane N1: analytic lemmas for the central small-ratio / normalized-collar checkers

Everything here is proved from GeneralCK corpus theorems and Mathlib; no numerical input.

* `neg_deriv_eta_sub_two_le` — SMALL_RATIO PROOF.md (5): `h(-η'(h)-2) ≤ (1 + 1/((1-v)ℓ(v)))/L`, `v = H⁻¹(h)`.
* `one_sub_mul_logit_anti` — `(1-v) log((1-v)/v)` is antitone on `(0,1/2]`.
* `eta_decrement_le_of_slope` — integrated form `η(y)-η(y') ≤ 2(y'-y) + K(log y' - log y)`.
* `entropyDrop_le` — Jensen gap `H(m)-(H a+H b)/2 ≤ d²/(2L(1-u²))` (SMALL_RATIO (3)).
* `log_one_add_div_anti` — `log(1+z)/z` is antitone (concavity of `log`).
* `C_mono` — `C(r) = 1 - H((1-r)/2)` is monotone on `[0,1]`.
-/

namespace CKLaneN1

open GeneralCK Set

/-! ## Entropy slope of `η` -/

theorem logit_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < Real.log ((1 - v) / v) := by
  apply Real.log_pos
  rw [lt_div_iff₀ hv]
  linarith

theorem logit_nonneg {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) : 0 ≤ Real.log ((1 - v) / v) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hv]
  linarith

/-- `(1-v) log((1-v)/v)` is antitone on `(0, 1/2]`. -/
theorem one_sub_mul_logit_anti {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (hw : w ≤ 1 / 2) :
    (1 - w) * Real.log ((1 - w) / w) ≤ (1 - v) * Real.log ((1 - v) / v) := by
  have hw0 : 0 < w := hv.trans_le hvw
  have hl0 : 0 ≤ Real.log ((1 - w) / w) := logit_nonneg hw0 hw
  have hl : Real.log ((1 - w) / w) ≤ Real.log ((1 - v) / v) := by
    apply Real.log_le_log (div_pos (by linarith) hw0)
    rw [div_le_div_iff₀ hw0 hv]
    nlinarith
  exact mul_le_mul (by linarith) hl hl0 (by linarith)

theorem binEntropy_eq_logit {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    Real.binEntropy v = v * Real.log ((1 - v) / v) - Real.log (1 - v) := by
  have hv1' : 0 < 1 - v := by linarith
  rw [Real.binEntropy, Real.log_inv, Real.log_inv, Real.log_div hv1'.ne' hv.ne']
  ring

/-- SMALL_RATIO PROOF.md (5): `h(-η'(h) - 2) ≤ (1 + 1/((1-v)ℓ))/L` with `v = H⁻¹(h)`, `ℓ = log((1-v)/v)`. -/
theorem neg_deriv_eta_sub_two_le {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    h * (-deriv eta h - 2) ≤
      (1 + 1 / ((1 - entropyInverse h) *
        Real.log ((1 - entropyInverse h) / entropyInverse h))) / Real.log 2 := by
  have hv : 0 < entropyInverse h := entropyInverse_pos h0 h1.le
  have hv' : entropyInverse h < 1 / 2 := entropyInverse_lt_half h0.le h1
  have hH : H (entropyInverse h) = h := (entropyInverse_spec h0.le h1.le).2.2
  rw [deriv_eta h0 h1]
  set v := entropyInverse h with hv_def
  set l := Real.log ((1 - v) / v) with hl_def
  have hlpos : 0 < l := logit_pos hv hv'
  have hL : 0 < Real.log 2 := log_two_pos
  have hv1 : 0 < 1 - v := by linarith
  have hJ : J v = l / Real.log 2 := rfl
  have hden : Real.log 2 * v * (1 - v) * J v = v * (1 - v) * l := by
    rw [hJ]
    field_simp
  have hLh : h * Real.log 2 = v * l - Real.log (1 - v) := by
    rw [← hH]
    unfold H
    rw [div_mul_cancel₀ _ hL.ne', binEntropy_eq_logit hv (by linarith)]
  have hN : -Real.log (1 - v) ≤ v / (1 - v) := by
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hv1)
    rw [Real.log_inv] at h2
    have e : (1 - v)⁻¹ - 1 = v / (1 - v) := by
      field_simp
      ring
    linarith
  have hN0 : 0 ≤ -Real.log (1 - v) := by
    have := Real.log_nonpos hv1.le (by linarith : 1 - v ≤ 1)
    linarith
  rw [hden]
  have hvv : 0 < v * (1 - v) * l := by positivity
  have hsimp : h * (-(-2 - (1 - 2 * v) / (v * (1 - v) * l)) - 2) =
      h * (1 - 2 * v) / (v * (1 - v) * l) := by
    ring
  rw [hsimp, le_div_iff₀ hL, div_mul_eq_mul_div, div_le_iff₀ hvv]
  have hrhs : (1 + 1 / ((1 - v) * l)) * (v * (1 - v) * l) = v * (1 - v) * l + v := by
    field_simp
  rw [hrhs]
  have key : h * Real.log 2 * (1 - 2 * v) ≤ v * (1 - v) * l + v := by
    rw [hLh]
    have hq : (1 - 2 * v) * (v / (1 - v)) ≤ v := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ hv1]
      nlinarith
    have h12 : 0 ≤ 1 - 2 * v := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hN h12, mul_nonneg hv.le hlpos.le]
  nlinarith [key]

/-- The slope bound with a rational-friendly upper bracket `v ≤ vh` and `0 < lo ≤ log((1-vh)/vh)`. -/
theorem neg_deriv_eta_sub_two_le_bracket {h vh lo L0 : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (hvh : vh ≤ 1 / 2) (hHv : h ≤ H vh) (hlo : 0 < lo) (hlog : lo ≤ Real.log ((1 - vh) / vh))
    (hL0 : 0 < L0) (hL0le : L0 ≤ Real.log 2) :
    h * (-deriv eta h - 2) ≤ (1 + 1 / ((1 - vh) * lo)) / L0 := by
  have hv : 0 < entropyInverse h := entropyInverse_pos h0 h1.le
  have hv' : entropyInverse h < 1 / 2 := entropyInverse_lt_half h0.le h1
  have hvh0 : 0 < vh := by
    by_contra hn
    have hvh0 : vh ≤ 0 := le_of_not_gt hn
    have hHle : H vh ≤ 0 := by
      rcases eq_or_lt_of_le hvh0 with he | hlt
      · rw [he, H_zero]
      · have : Real.binEntropy vh < 0 := Real.binEntropy_neg_of_neg hlt
        unfold H
        exact div_nonpos_of_nonpos_of_nonneg this.le log_two_pos.le
    linarith
  have hmono : entropyInverse h ≤ vh := by
    have hvh_inv : entropyInverse (H vh) = vh := entropyInverse_H_lower hvh0.le hvh
    have := entropyInverse_mono h0.le (H_le_one vh) hHv
    rwa [hvh_inv] at this
  have hanti := one_sub_mul_logit_anti hv hmono hvh
  have hvh1 : 0 < 1 - vh := by linarith
  have hbr : 0 < (1 - vh) * lo := mul_pos hvh1 hlo
  have hprod : (1 - vh) * lo ≤ (1 - entropyInverse h) *
      Real.log ((1 - entropyInverse h) / entropyInverse h) :=
    (mul_le_mul_of_nonneg_left hlog hvh1.le).trans hanti
  have hbase := neg_deriv_eta_sub_two_le h0 h1
  have hinv : 1 / ((1 - entropyInverse h) *
      Real.log ((1 - entropyInverse h) / entropyInverse h)) ≤ 1 / ((1 - vh) * lo) :=
    one_div_le_one_div_of_le hbr hprod
  have hnum : 0 ≤ 1 + 1 / ((1 - vh) * lo) := by positivity
  have hL := log_two_pos
  calc h * (-deriv eta h - 2)
      ≤ (1 + 1 / ((1 - entropyInverse h) *
          Real.log ((1 - entropyInverse h) / entropyInverse h))) / Real.log 2 := hbase
    _ ≤ (1 + 1 / ((1 - vh) * lo)) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hL.le
    _ ≤ (1 + 1 / ((1 - vh) * lo)) / L0 := div_le_div_of_nonneg_left hnum hL0 hL0le

/-- Integrated slope bound: `η(y) - η(y') ≤ 2(y'-y) + K (log y' - log y)`. -/
theorem eta_decrement_le_of_slope {y y' K : ℝ} (hy : 0 < y) (hyy : y ≤ y') (hy1 : y' < 1)
    (hK : ∀ h ∈ Icc y y', h * (-deriv eta h - 2) ≤ K) :
    eta y - eta y' ≤ 2 * (y' - y) + K * (Real.log y' - Real.log y) := by
  have hmono : MonotoneOn (fun h => eta h + 2 * h + K * Real.log h) (Icc y y') := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc y y')
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
      have : -deriv eta h - 2 ≤ K / h := by
        rw [le_div_iff₀ h0]
        linarith
      linarith
  have := hmono ⟨le_refl y, hyy⟩ ⟨hyy, le_refl y'⟩ hyy
  simp only at this
  linarith

/-! ## Jensen gap of binary entropy -/

/-- SMALL_RATIO PROOF.md (3): the entropy Jensen gap with the second-derivative bound. -/
theorem entropyDrop_le {a b u : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hu : u < 1)
    (hua : |1 - 2 * a| ≤ u) (hub : |1 - 2 * b| ≤ u) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (b - a) ^ 2 / (2 * Real.log 2 * (1 - u ^ 2)) := by
  have hL : 0 < Real.log 2 := log_two_pos
  have hu0 : 0 ≤ u := (abs_nonneg _).trans hua
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith
  set M : ℝ := 4 / (Real.log 2 * (1 - u ^ 2)) with hM
  have hMpos : 0 < M := by positivity
  set m : ℝ := (a + b) / 2 with hm
  -- pointwise variance bound on [a, b]
  have hvar : ∀ z ∈ Icc a b, (1 - u ^ 2) / 4 ≤ z * (1 - z) := by
    intro z hz
    have h1 : |1 - 2 * z| ≤ u := by
      rw [abs_le] at hua hub ⊢
      constructor <;> nlinarith [hz.1, hz.2]
    have h2 : (1 - 2 * z) ^ 2 ≤ u ^ 2 := by
      have := sq_abs (1 - 2 * z)
      nlinarith [abs_nonneg (1 - 2 * z)]
    nlinarith
  have hconv : ConvexOn ℝ (Icc a b) (fun z => H z + M / 2 * (z - m) ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (f' := fun z => (Real.log (1 - z) - Real.log z) / Real.log 2 + M * (z - m))
      (f'' := fun z => (-(1 - z)⁻¹ - z⁻¹) / Real.log 2 + M)
    · have hc : Continuous (fun z => H z + M / 2 * (z - m) ^ 2) := by
        exact H_continuous.add (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))
      exact hc.continuousOn
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := ha.trans hz.1
      have hz1 : z < 1 := lt_trans hz.2 hb
      have e1 : HasDerivAt H ((Real.log (1 - z) - Real.log z) / Real.log 2) z :=
        (Real.hasDerivAt_binEntropy hz0.ne' hz1.ne).div_const (Real.log 2)
      have e2 : HasDerivAt (fun y : ℝ => M / 2 * (y - m) ^ 2) (M * (z - m)) z := by
        have h1 : HasDerivAt (fun y : ℝ => y - m) 1 z := (hasDerivAt_id' z).sub_const m
        have h2 : HasDerivAt (fun y : ℝ => M / 2 * (y - m) ^ 2) _ z := (h1.pow 2).const_mul (M / 2)
        refine h2.congr_deriv ?_
        ring
      exact (e1.add e2).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := ha.trans hz.1
      have hz1 : z < 1 := lt_trans hz.2 hb
      have e1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-(1 - z)⁻¹) z := by
        have h1 := ((hasDerivAt_id z).const_sub 1).log (by simp only [id_eq]; linarith)
        have heq : -1 / (1 - id z) = -(1 - z)⁻¹ := by
          simp only [id_eq]
          ring
        rw [heq] at h1
        exact h1
      have e2 : HasDerivAt (fun y : ℝ => Real.log y) z⁻¹ z := Real.hasDerivAt_log hz0.ne'
      have e3 : HasDerivAt (fun y : ℝ => M * (y - m)) M z := by
        have h3 := ((hasDerivAt_id z).sub_const m).const_mul M
        rw [mul_one] at h3
        exact h3
      exact (((e1.sub e2).div_const (Real.log 2)).add e3).hasDerivWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := ha.trans hz.1
      have hz1 : z < 1 := lt_trans hz.2 hb
      have hv := hvar z ⟨hz.1.le, hz.2.le⟩
      have hzz : 0 < z * (1 - z) := mul_pos hz0 (by linarith)
      have e : (-(1 - z)⁻¹ - z⁻¹) = -(1 / (z * (1 - z))) := by
        have h1z : (1 - z) ≠ 0 := by linarith
        field_simp
        ring
      show 0 ≤ (-(1 - z)⁻¹ - z⁻¹) / Real.log 2 + M
      rw [e]
      have hb1 : 1 / (z * (1 - z)) ≤ 4 / (1 - u ^ 2) := by
        rw [div_le_div_iff₀ hzz hu2]
        linarith
      have hb2 : 1 / (z * (1 - z)) / Real.log 2 ≤ M := by
        have hMeq : M = 4 / (1 - u ^ 2) / Real.log 2 := by
          rw [hM, div_div, mul_comm (1 - u ^ 2) (Real.log 2)]
        rw [hMeq]
        exact div_le_div_of_nonneg_right hb1 hL.le
      have : -(1 / (z * (1 - z))) / Real.log 2 = -(1 / (z * (1 - z)) / Real.log 2) := by ring
      linarith
  have hj := hconv.2 (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hj
  have hmid : (1 / 2 : ℝ) * a + 1 / 2 * b = m := by rw [hm]; ring
  rw [hmid] at hj
  have hsq1 : (a - m) ^ 2 = (b - a) ^ 2 / 4 := by rw [hm]; ring
  have hsq2 : (b - m) ^ 2 = (b - a) ^ 2 / 4 := by rw [hm]; ring
  rw [hsq1, hsq2, show (m - m) ^ 2 = 0 by ring] at hj
  have hMval : M / 2 * ((b - a) ^ 2 / 4) = (b - a) ^ 2 / (2 * Real.log 2 * (1 - u ^ 2)) := by
    rw [hM]
    field_simp
  have : H m ≤ (H a + H b) / 2 + M / 2 * ((b - a) ^ 2 / 4) := by linarith
  rw [hMval] at this
  linarith

/-! ## Small scalar facts -/

/-- `log(1+z)/z` is antitone on `(0,∞)`, in the product form. -/
theorem log_one_add_div_anti {z₁ z₂ : ℝ} (h1 : 0 < z₁) (h12 : z₁ ≤ z₂) :
    z₁ * Real.log (1 + z₂) ≤ z₂ * Real.log (1 + z₁) := by
  have h2 : 0 < z₂ := h1.trans_le h12
  have hconc := (strictConcaveOn_log_Ioi).concaveOn.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 1 + z₂ ∈ Ioi (0 : ℝ) by simp; linarith)
    (show (0 : ℝ) ≤ 1 - z₁ / z₂ by rw [sub_nonneg, div_le_one h2]; exact h12)
    (show (0 : ℝ) ≤ z₁ / z₂ by positivity) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
  have e : (1 - z₁ / z₂) * 1 + z₁ / z₂ * (1 + z₂) = 1 + z₁ := by field_simp; ring
  rw [e] at hconc
  have := mul_le_mul_of_nonneg_left hconc h2.le
  rw [show z₂ * (z₁ / z₂ * Real.log (1 + z₂)) = z₁ * Real.log (1 + z₂) by field_simp] at this
  linarith

/-- `log(1+Z) ≤ Z * ℓ` whenever `Z ≥ z > 0` and `log(1+z) ≤ z * ℓ`. -/
theorem log_one_add_le_of_anchor {z Z ℓ : ℝ} (hz : 0 < z) (hzZ : z ≤ Z)
    (hℓ : Real.log (1 + z) ≤ z * ℓ) : Real.log (1 + Z) ≤ Z * ℓ := by
  have hZ : 0 < Z := hz.trans_le hzZ
  have ha := log_one_add_div_anti hz hzZ
  have : z * Real.log (1 + Z) ≤ z * (Z * ℓ) := by nlinarith
  exact le_of_mul_le_mul_left this hz

theorem log_one_add_le_self {Z : ℝ} (hZ : 0 ≤ Z) : Real.log (1 + Z) ≤ Z := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + Z by linarith)
  linarith

/-- `C(r) = 1 - H((1-r)/2)` is monotone on `[0,1]`. -/
theorem C_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    1 - H ((1 - r) / 2) ≤ 1 - H ((1 - s) / 2) := by
  have h := H_strictMonoOn.monotoneOn (a := (1 - s) / 2) (b := (1 - r) / 2)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  linarith

end CKLaneN1

end


