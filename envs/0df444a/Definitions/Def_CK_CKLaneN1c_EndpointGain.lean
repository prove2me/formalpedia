-- Prove2me | Definitions.Def_CK_CKLaneN1c_EndpointGain
-- name    : CK_CKLaneN1c_EndpointGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:39:45.080499+00:00
-- url     : https://prove2.me/theorems/2df0a558-da24-4a0d-99f4-b3a6b1fe7e02
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.EndpointGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.EndpointGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.EndpointGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.EndpointGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/EndpointGain.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointContactGain
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGlobal
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneD_Analytic

-- ===== source module CKLaneN1c.EndpointGain =====
section

/-!
# Lane N1c-c: the endpoint entropy-imbalance gain for `d ≥ 4E` (TRANSVERSE_STRIP §2, (3))

Archive: `CK_NO_SEPARATION_EXTENSION/prior_inputs/TRANSVERSE_STRIP.md` §2, used by
`CK_OPPOSITE_EXTENSION/transition/PROOF.md` (5):

  `B_end ≥ F(d,E) + (9d/(20L)) 𝒥(τ)`,  `𝒥(τ) = -log(1-τ²)`,  `τ = (e-f)/(e+f)`,  for `d/E ≥ 4`.

Scalar input: `Q''(h) ≥ 9/(10 L h²)` on `(0, 37/80]` for `Q = J ∘ H⁻¹` (`curvature_lower_nine`), since
`v = H⁻¹(h) ≤ 1/10` there (`H(1/10) ≥ 37/80`) and `log 9 ≥ 2197/1000`.  At the equal-entropy contact
of ratio `≥ 4`, `E/p̄ = H(u) ≤ 37/160` (`equal_mass_ratio_le`), so both split arguments stay in
`(0, 37/80]`.  The global supporting plane (`Contact.value_le_cost`) transfers the contact value to the
cost of every finite law (`law_endpoint_gain_four`).  The corpus analogue for `d ≥ 8E` with factor
`1/(2L)` is `GeneralCK.PsiEndpointPlane.law_endpoint_logarithmic_lower`; the proof below follows it.
All numerical constants are certified by `CKLaneE.FP` enclosures evaluated in the kernel.
-/

set_option autoImplicit false

namespace CKLaneN1c.Gain

open GeneralCK GeneralCK.PsiEndpointLogGain GeneralCK.PsiSignedSplit Set

/-! ## Certified constants -/

theorem H_tenth_ge : (37 / 80 : ℝ) ≤ H (1 / 10) := by
  have hpt : CKLaneE.FP.ptOk (1 / 10) = true := by decide +kernel
  have h := (CKLaneE.FP.H_bounds hpt).1
  have h2 : (37 / 80 : ℚ) ≤ CKLaneE.FP.Hlo (1 / 10) := by decide +kernel
  have h3 : ((37 / 80 : ℚ) : ℝ) ≤ ((CKLaneE.FP.Hlo (1 / 10) : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h h3
  linarith

theorem H_380_le : H (3 / 80) ≤ (37 / 160 : ℝ) := by
  have hpt : CKLaneE.FP.ptOk (3 / 80) = true := by decide +kernel
  have h := (CKLaneE.FP.H_bounds hpt).2
  have h2 : CKLaneE.FP.Hhi (3 / 80) ≤ (37 / 160 : ℚ) := by decide +kernel
  have h3 : ((CKLaneE.FP.Hhi (3 / 80) : ℚ) : ℝ) ≤ ((37 / 160 : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h h3
  linarith

theorem log_nine_lower : (2197 / 1000 : ℝ) ≤ Real.log 9 := by
  have hpt : CKLaneE.FP.ptOk (1 / 9) = true := by decide +kernel
  have h := (CKLaneE.FP.ptOk_sound hpt).2.1
  have h2 : (2197 / 1000 : ℚ) ≤ -CKLaneE.FP.lHi (1 / 9) := by decide +kernel
  have h3 : ((2197 / 1000 : ℚ) : ℝ) ≤ ((-CKLaneE.FP.lHi (1 / 9) : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h h3
  have e : Real.log (1 / 9 : ℝ) = -Real.log 9 := by
    rw [one_div, Real.log_inv]
  rw [e] at h
  linarith

/-! ## `Q'' ≥ 9/(10 L h²)` on `(0, 37/80]` -/

theorem logit_product_le_one' {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    v * Real.log ((1 - v) / v) ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - v) hv)) hv.le
  have he : v * ((1 - v) / v - 1) = 1 - 2 * v := by field_simp; ring
  rw [he] at hh
  linarith

/-- TRANSVERSE_STRIP (2): `9(1-v)² ℓ³ ≤ 10((1-2v)ℓ - 1)(ℓ+1)²` for `0 < v ≤ 1/10`, `ℓ ≥ 2197/1000`. -/
theorem poly_nine {v l : ℝ} (hv : 0 < v) (hvi : v ≤ 1 / 10) (hl : 2197 / 1000 ≤ l) :
    9 * (1 - v) ^ 2 * l ^ 3 ≤ 10 * ((1 - 2 * v) * l - 1) * (l + 1) ^ 2 := by
  have hl0 : 0 ≤ l := by linarith
  have hs : 0 ≤ l - 2197 / 1000 := by linarith
  have hg : 0 ≤ (71 / 100) * l ^ 3 + 6 * l ^ 2 - 12 * l - 10 := by
    nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs]
  have hbr : 0 ≤ 20 * l * (l + 1) ^ 2 - 9 * l ^ 3 * (19 / 10 - v) := by
    nlinarith [mul_nonneg (mul_nonneg hl0 hl0) hl0, mul_nonneg (mul_nonneg (mul_nonneg hl0 hl0) hl0) hv.le,
      mul_nonneg hl0 hl0]
  have hkey : 10 * ((1 - 2 * v) * l - 1) * (l + 1) ^ 2 - 9 * (1 - v) ^ 2 * l ^ 3 =
      ((71 / 100) * l ^ 3 + 6 * l ^ 2 - 12 * l - 10) +
        (1 / 10 - v) * (20 * l * (l + 1) ^ 2 - 9 * l ^ 3 * (19 / 10 - v)) := by ring
  have hprod := mul_nonneg (show (0 : ℝ) ≤ 1 / 10 - v by linarith) hbr
  linarith

/-- Logarithmic curvature of `J ∘ entropyInverse` with factor `9/10` on `(0, 37/80]`. -/
theorem curvature_lower_nine {h : ℝ} (hh : 0 < h) (hhi : h ≤ 37 / 80) :
    9 / (10 * (Real.log 2 * h ^ 2)) ≤ curvature h := by
  let v := entropyInverse h
  let l := Real.log ((1 - v) / v)
  have hv : 0 < v := entropyInverse_pos hh (by linarith)
  have hvi : v ≤ 1 / 10 := by
    have hm := entropyInverse_mono hh.le (H_le_one (1 / 10)) (hhi.trans H_tenth_ge)
    rwa [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num)] at hm
  have hv1 : v < 1 := by linarith
  have hl : 2197 / 1000 ≤ l := by
    have hr : (9 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).mpr (by linarith)
    exact log_nine_lower.trans (Real.log_le_log (by norm_num) hr)
  have hp := poly_nine hv hvi hl
  have hn := PsiExtendedEntropyCurvature.entropy_natural_lower hv hv1
  have he : H v = h := (entropyInverse_spec hh.le (by linarith)).2.2
  rw [he] at hn
  have hsq : (v * (l + 1)) ^ 2 ≤ (h * Real.log 2) ^ 2 := by
    have hb : 0 ≤ v * (l + 1) := by positivity
    nlinarith only [hn, hb]
  have hN : 0 ≤ (1 - 2 * v) * l - 1 := by nlinarith
  have hs := mul_le_mul_of_nonneg_right hsq hN
  have hp' := mul_le_mul_of_nonneg_left hp (sq_nonneg v)
  have hl0 : 0 < l := by linarith
  change 9 / (10 * (Real.log 2 * h ^ 2)) ≤
    Real.log 2 * ((1 - 2 * v) * l - 1) / (v ^ 2 * (1 - v) ^ 2 * l ^ 3)
  have hL := log_two_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity : 0 < v ^ 2 * (1 - v) ^ 2 * l ^ 3)]
  nlinarith only [hs, hp']

/-! ## Convexity of `Q + (9/10) log / L` and the split gain -/

/-- `Q h + (9/10) log h / L`. -/
noncomputable def comp9 (h : ℝ) : ℝ := Q h + 9 / 10 * (Real.log h / Real.log 2)

theorem hasDerivAt_comp9 {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt comp9 (slope h + 9 / 10 * ((1 / Real.log 2) / h)) h := by
  have h1 := hasDerivAt_Q hh hh1
  have h2 := ((Real.hasDerivAt_log hh.ne').div_const (Real.log 2)).const_mul (9 / 10 : ℝ)
  have h3 := h1.add h2
  have e : slope h + 9 / 10 * (h⁻¹ / Real.log 2) = slope h + 9 / 10 * ((1 / Real.log 2) / h) := by
    field_simp
  rw [e] at h3
  exact h3

theorem hasDerivAt_comp9_slope {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (fun x => slope x + 9 / 10 * ((1 / Real.log 2) / x))
      (curvature h - 9 / 10 / (Real.log 2 * h ^ 2)) h := by
  have h1 := hasDerivAt_slope hh hh1
  have h2 := ((hasDerivAt_const h (1 / Real.log 2)).div (hasDerivAt_id h) hh.ne').const_mul
    (9 / 10 : ℝ)
  convert! h1.add h2 using 1
  dsimp
  ring

theorem comp9_convexOn : ConvexOn ℝ (Ioc 0 (37 / 80)) comp9 := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 (37 / 80))
    (f' := fun h => slope h + 9 / 10 * ((1 / Real.log 2) / h))
    (f'' := fun h => curvature h - 9 / 10 / (Real.log 2 * h ^ 2))
  · intro h hh
    exact (hasDerivAt_comp9 hh.1 (by linarith [hh.2])).continuousAt.continuousWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_comp9 hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_comp9_slope hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    have hc := curvature_lower_nine hi.1 hi.2
    have e : 9 / 10 / (Real.log 2 * h ^ 2) = 9 / (10 * (Real.log 2 * h ^ 2)) := by
      rw [div_div]
    rw [e]
    linarith

/-- The endpoint log gain with factor `9/10`, uniform over every positive split. -/
theorem Q_split_gain9 {h t : ℝ} (hh : 0 < h) (hhi : h ≤ 37 / 160) (ht : |t| < 1) :
    Q h + 9 / 10 * (barrier t / (2 * Real.log 2)) ≤
      (Q (h * (1 + t)) + Q (h * (1 - t))) / 2 := by
  have hi := abs_lt.mp ht
  have hp : 0 < h * (1 + t) := mul_pos hh (by linarith)
  have hm : 0 < h * (1 - t) := mul_pos hh (by linarith)
  have hpu : h * (1 + t) ≤ 37 / 80 := by nlinarith
  have hmu : h * (1 - t) ≤ 37 / 80 := by nlinarith
  have hj := comp9_convexOn.2 ⟨hp, hpu⟩ ⟨hm, hmu⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show (1 / 2 : ℝ) * (h * (1 + t)) + (1 / 2) * (h * (1 - t)) = h by ring] at hj
  unfold comp9 at hj
  rw [Real.log_mul hh.ne' (by linarith : 1 + t ≠ 0),
    Real.log_mul hh.ne' (by linarith : 1 - t ≠ 0)] at hj
  unfold barrier
  rw [log_one_sub_sq ht]
  linear_combination hj

/-! ## The contact value and the finite-law cost -/

/-- At the equal-entropy contact of ratio at least four, `E / p̄ = H(u) ≤ 37/160`. -/
theorem equal_mass_ratio_le {d E : ℝ} (cbar : PsiEndpointContact.Contact d E E)
    (hd : 4 * E ≤ d) : E / cbar.mass ≤ 37 / 160 := by
  have hm := cbar.mass_pos
  have hEeq := cbar.entropy_left_eq
  have hrc := cbar.equal_radialContact
  have hdpos := cbar.difference_pos
  have hE : 0 < E := cbar.entropy_left_pos
  have heq := radialContact_equation hdpos hE
  rw [hrc] at heq
  have hratio : E / cbar.mass = H cbar.left :=
    (div_eq_iff hm.ne').mpr (by rw [mul_comm]; exact hEeq)
  rw [hratio]
  have hu0 := cbar.left_pos
  have hu1 := cbar.left_lt_half
  have hHnn : 0 ≤ H cbar.left := H_nonneg hu0.le (by linarith)
  have hHu : 4 * H cbar.left ≤ 1 - 2 * cbar.left := by
    have h1 := mul_le_mul_of_nonneg_right hd hHnn
    have h2 : E * (4 * H cbar.left) ≤ E * (1 - 2 * cbar.left) := by nlinarith
    exact le_of_mul_le_mul_left h2 hE
  rcases le_or_gt (3 / 80) cbar.left with hu | hu
  · linarith
  · have h1 := CKLaneD.H_mono_left hu0.le hu.le (by norm_num)
    linarith [H_380_le]

/-- The ratio-four endpoint value inequality, for every strictly positive entropy split. -/
theorem value_gain_four {d e f : ℝ} (c : PsiEndpointContact.Contact d e f)
    (hd : 4 * ((e + f) / 2) ≤ d) :
    F d ((e + f) / 2) + 9 * d / (20 * Real.log 2) * barrier ((e - f) / (e + f)) ≤ c.value := by
  have he := c.entropy_left_pos
  have hf := c.entropy_right_pos
  have hE : 0 < (e + f) / 2 := by linarith
  obtain ⟨cbar⟩ := c.exists_equal_contact
  have hbar : 0 < (e + f) / 2 / cbar.mass := div_pos hE cbar.mass_pos
  have hbarcap : (e + f) / 2 / cbar.mass ≤ 37 / 160 := equal_mass_ratio_le cbar hd
  obtain ⟨ht, het, hft⟩ := PsiRetainedChildBridge.positive_entropy_split he hf
  have hplus : ((e + f) / 2 / cbar.mass) * (1 + (e - f) / (e + f)) = e / cbar.mass := by
    calc _ = ((e + f) / 2 * (1 + (e - f) / (e + f))) / cbar.mass := by ring
      _ = e / cbar.mass := by rw [het]
  have hminus : ((e + f) / 2 / cbar.mass) * (1 - (e - f) / (e + f)) = f / cbar.mass := by
    calc _ = ((e + f) / 2 * (1 - (e - f) / (e + f))) / cbar.mass := by ring
      _ = f / cbar.mass := by rw [hft]
  have hgain := Q_split_gain9 hbar hbarcap ht
  rw [hplus, hminus] at hgain
  have hdpos := c.difference_pos
  have hmul := mul_le_mul_of_nonneg_left hgain hdpos.le
  have hlast := c.value_ge_equal_mass_Q cbar (by linarith)
  have hFq := cbar.F_eq_equal_Q
  have hbound : F d ((e + f) / 2) + 9 * d / (20 * Real.log 2) * barrier ((e - f) / (e + f)) ≤
      d / 2 * (Q (e / cbar.mass) + Q (f / cbar.mass)) := by
    rw [hFq]
    have hL := log_two_pos
    have e1 : d * (Q ((e + f) / 2 / cbar.mass) +
        9 / 10 * (barrier ((e - f) / (e + f)) / (2 * Real.log 2))) =
        d * Q ((e + f) / 2 / cbar.mass) + 9 * d / (20 * Real.log 2) * barrier ((e - f) / (e + f)) := by
      field_simp
      ring
    have e2 : d * ((Q (e / cbar.mass) + Q (f / cbar.mass)) / 2) =
        d / 2 * (Q (e / cbar.mass) + Q (f / cbar.mass)) := by ring
    rw [e1, e2] at hmul
    exact hmul
  exact hbound.trans hlast

/-- Endpoint entropy-allocation gain for every finite interior law with `d ≥ 4E`
(TRANSVERSE_STRIP (3), with all contact-existence and global-support obligations discharged). -/
theorem law_endpoint_gain_four {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hd : 4 * μ.meanEntropy ≤ μ.b - μ.a) :
    F (μ.b - μ.a) μ.meanEntropy + 9 * (μ.b - μ.a) / (20 * Real.log 2) *
      barrier ((μ.e - μ.f) / (μ.e + μ.f)) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  obtain ⟨c⟩ := PsiEndpointContact.exists_contact_of_feasible
    ⟨μ.a_interior.1.le, μ.a_interior.2.le⟩
    ⟨μ.b_interior.1.le, μ.b_interior.2.le⟩
    μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap (by linarith : μ.meanEntropy < μ.b - μ.a)
  exact (value_gain_four c hd).trans (c.value_le_cost μ)

end CKLaneN1c.Gain

end


