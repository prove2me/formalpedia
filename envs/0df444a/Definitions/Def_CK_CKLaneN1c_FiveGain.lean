-- Prove2me | Definitions.Def_CK_CKLaneN1c_FiveGain
-- name    : CK_CKLaneN1c_FiveGain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T12:50:45.491884+00:00
-- url     : https://prove2.me/theorems/f51a467d-3d5c-466b-bb9c-ac968cb66187
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.FiveGain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.FiveGain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.FiveGain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.FiveGain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/FiveGain.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGlobal
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail

-- ===== source module CKLaneN1c.FiveGain =====
section

/-!
# Endpoint logarithmic gain at separation ratio five

Lane N1c-c copy of the corpus source `GeneralCK/PsiEndpointFiveGain.lean`
(`~/ck_tasks_0914/payload/GeneralCK/`, sha256 94ed6f6fc3a97d93afc28ed1ba79b4004f45cd09802f17bcbbe83d8338e128d5), which is not compiled in the
F-C consumer root.  Only the namespace is changed (`GeneralCK.PsiEndpointFiveGain` →
`CKLaneN1c.FiveGain`, with `open GeneralCK`); every statement and proof is verbatim.
This is the SHARPER_COLLARS.md §1 input (2): `B_end ≥ F(d,E) + (d/(2L)) 𝒥(τ)` for `d ≥ 5E`.

The inverse-entropy logit curvature is proved through entropy 19/50. The
equal-entropy contact has entropy coordinate at most 19/100 when d≥5E,
including arbitrarily large d/E, so the compensated Jensen argument covers
every strictly positive entropy split at the manuscript's ratio-five threshold.
-/

namespace CKLaneN1c.FiveGain
open GeneralCK Set GeneralCK.PsiEndpointLogGain GeneralCK.PsiSignedSplit

private theorem log_37_24_lower : (43 / 100 : ℝ) ≤ Real.log (37 / 24) := by
  have h := Certificates.checkLog_sound (w := 13 / 61) (n := 3)
    (lo := 43 / 100) (hi := 1)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.1

theorem log_37_3_lower : (5 / 2 : ℝ) ≤ Real.log (37 / 3) := by
  have he : Real.log (37 / 3 : ℝ) = 3 * Real.log 2 + Real.log (37 / 24) := by
    rw [show (37 / 3 : ℝ) = 2 ^ (3 : ℕ) * (37 / 24) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  rw [he]
  linarith [log_37_24_lower]

private theorem log_40_37_lower : (77 / 1000 : ℝ) ≤ Real.log (40 / 37) := by
  have h := Certificates.checkLog_sound (w := 3 / 77) (n := 2)
    (lo := 77 / 1000) (hi := 1 / 10)
    (by norm_num [Certificates.checkLog, Certificates.logLower,
      Certificates.logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h.1

private theorem entropy_logit_identity {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    H v * Real.log 2 = v * Real.log ((1 - v) / v) - Real.log (1 - v) := by
  unfold H Real.binEntropy
  rw [div_mul_cancel₀ _ log_two_pos.ne', Real.log_div (by linarith) hv.ne']
  simp only [Real.log_inv]
  ring

theorem entropy_3_40_lower : (19 / 50 : ℝ) ≤ H (3 / 40) := by
  have he := entropy_logit_identity (v := 3 / 40) (by norm_num) (by norm_num)
  have hc : (77 / 1000 : ℝ) ≤ -Real.log (1 - (3 / 40 : ℝ)) := by
    have hh := log_40_37_lower
    rw [show (40 / 37 : ℝ) = (1 - (3 / 40 : ℝ))⁻¹ by norm_num, Real.log_inv] at hh
    exact hh
  have hl : (5 / 2 : ℝ) ≤ Real.log ((1 - (3 / 40 : ℝ)) / (3 / 40)) := by
    norm_num
    exact log_37_3_lower
  have hL := Certificates.PilotData.log_two.2
  norm_num only [div_one] at hL
  apply (mul_le_mul_iff_right₀ log_two_pos).mp
  nlinarith only [he, hc, hl, hL]

theorem entropy_inverse_le_three_fortieths {h : ℝ} (hh : 0 < h) (hhi : h ≤ 19 / 50) :
    entropyInverse h ≤ 3 / 40 := by
  have hm := entropyInverse_mono hh.le (H_le_one (3 / 40))
    (hhi.trans entropy_3_40_lower)
  rwa [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 3 / 40) (by norm_num)] at hm

private theorem logit_product_le_one {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    v * Real.log ((1 - v) / v) ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - v) hv)) hv.le
  have he : v * ((1 - v) / v - 1) = 1 - 2 * v := by field_simp; ring
  rw [he] at hh
  linarith

private theorem curvature_polynomial {v l : ℝ} (hv : 0 < v)
    (hvi : v ≤ 3 / 40) (hl : 5 / 2 ≤ l) (hvl : v * l ≤ 1) :
    (1 - v) ^ 2 * l ^ 3 ≤ ((1 - 2 * v) * l - 1) * (l + 1) ^ 2 := by
  have hv2l : v ^ 2 * l ≤ v := by nlinarith [mul_le_mul_of_nonneg_left hvl hv.le]
  have hcoef : 5 / 8 ≤ 1 - 4 * v - v ^ 2 * l := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg l)
  have hlin : (1 + 2 * v) * l ≤ (23 / 20) * l :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hquad : 0 ≤ (5 / 8) * l ^ 2 - (23 / 20) * l - 1 := by nlinarith
  nlinarith only [hmul, hlin, hquad]

theorem curvature_lower {h : ℝ} (hh : 0 < h) (hhi : h ≤ 19 / 50) :
    1 / (Real.log 2 * h ^ 2) ≤ curvature h := by
  let v := entropyInverse h
  let l := Real.log ((1 - v) / v)
  have hv : 0 < v := entropyInverse_pos hh (by linarith)
  have hvi : v ≤ 3 / 40 := entropy_inverse_le_three_fortieths hh hhi
  have hv1 : v < 1 := by linarith
  have hl : 5 / 2 ≤ l := by
    have hr : (37 / 3 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).mpr (by linarith)
    exact log_37_3_lower.trans (Real.log_le_log (by norm_num) hr)
  have hvl := logit_product_le_one hv hv1
  have hp := curvature_polynomial hv hvi hl hvl
  have hn := PsiExtendedEntropyCurvature.entropy_natural_lower hv hv1
  have he : H v = h := (entropyInverse_spec hh.le (by linarith)).2.2
  rw [he] at hn
  have hsq : (v * (l + 1)) ^ 2 ≤ (h * Real.log 2) ^ 2 := by
    have hb : 0 ≤ v * (l + 1) := by positivity
    nlinarith only [hn, hb]
  have hN : 0 ≤ (1 - 2 * v) * l - 1 := by
    have hb := mul_le_mul (show (17 / 20 : ℝ) ≤ 1 - 2 * v by linarith) hl
      (by norm_num : (0 : ℝ) ≤ 5 / 2) (by linarith : 0 ≤ 1 - 2 * v)
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hsq hN
  have hp' := mul_le_mul_of_nonneg_left hp (sq_nonneg v)
  change 1 / (Real.log 2 * h ^ 2) ≤
    Real.log 2 * ((1 - 2 * v) * l - 1) / (v ^ 2 * (1 - v) ^ 2 * l ^ 3)
  apply (div_le_div_iff₀ (by positivity)
    (by positivity : 0 < v ^ 2 * (1 - v) ^ 2 * l ^ 3)).mpr
  nlinarith only [hs, hp']

private theorem hasDerivAt_compensated_slope {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (fun x => slope x + (1 / Real.log 2) / x)
      (curvature h - 1 / (Real.log 2 * h ^ 2)) h := by
  convert! (hasDerivAt_slope hh hh1).add
    ((hasDerivAt_const h (1 / Real.log 2)).div (hasDerivAt_id h) hh.ne') using 1
  dsimp
  ring

theorem compensated_convexOn : ConvexOn ℝ (Ioc 0 (19 / 50)) compensated := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 (19 / 50))
    (f' := fun h => slope h + (1 / Real.log 2) / h)
    (f'' := fun h => curvature h - 1 / (Real.log 2 * h ^ 2))
  · intro h hh
    exact (hasDerivAt_compensated hh.1 (by linarith [hh.2])).continuousAt.continuousWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_compensated hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact (hasDerivAt_compensated_slope hi.1 (by linarith [hi.2])).hasDerivWithinAt
  · intro h hh
    have hi := interior_subset hh
    exact sub_nonneg.mpr (curvature_lower hi.1 hi.2)

theorem Q_split_gain {h t : ℝ} (hh : 0 < h) (hhi : h ≤ 19 / 100) (ht : |t| < 1) :
    Q h + barrier t / (2 * Real.log 2) ≤
      (Q (h * (1 + t)) + Q (h * (1 - t))) / 2 := by
  have hi := abs_lt.mp ht
  have hp : 0 < h * (1 + t) := mul_pos hh (by linarith)
  have hm : 0 < h * (1 - t) := mul_pos hh (by linarith)
  have hpu : h * (1 + t) ≤ 19 / 50 := by nlinarith
  have hmu : h * (1 - t) ≤ 19 / 50 := by nlinarith
  have hj := compensated_convexOn.2 ⟨hp, hpu⟩ ⟨hm, hmu⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show (1 / 2 : ℝ) * (h * (1 + t)) + (1 / 2) * (h * (1 - t)) = h by ring] at hj
  unfold compensated at hj
  rw [Real.log_mul hh.ne' (by linarith : 1 + t ≠ 0),
    Real.log_mul hh.ne' (by linarith : 1 - t ≠ 0)] at hj
  unfold barrier
  rw [log_one_sub_sq ht]
  linear_combination hj

/-- This bound is uniform for all ratios at least five. The contact coordinate
need not stay above 1/40: both sides of that cutoff are handled explicitly. -/
theorem equal_contact_entropy_bound {d E : ℝ}
    (cbar : PsiEndpointContact.Contact d E E) (hd : 5 * E ≤ d) :
    E / cbar.mass ≤ 19 / 100 := by
  have hbarH : E / cbar.mass = H cbar.left := by
    apply (div_eq_iff cbar.mass_pos.ne').mpr
    nlinarith only [cbar.entropy_left_eq]
  by_cases hv : cbar.left ≤ 1 / 40
  · rw [hbarH]
    have hh := H_strictMonoOn.monotoneOn
      ⟨cbar.left_pos.le, cbar.left_lt_half.le⟩
      (show (1 / 40 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) by norm_num) hv
    linarith [PsiSameRatioTail.entropy_1_40_le]
  · apply (div_le_iff₀ cbar.mass_pos).mpr
    have hm : d ≤ (19 / 20) * cbar.mass := by
      calc
        d = cbar.mass * (1 - 2 * cbar.left) := by
          calc
            d = cbar.mass * (1 - cbar.left - cbar.right) := cbar.difference_eq
            _ = _ := by rw [← cbar.equal_coordinate_eq]; ring
        _ ≤ cbar.mass * (19 / 20) :=
          mul_le_mul_of_nonneg_left (by linarith [lt_of_not_ge hv]) cbar.mass_pos.le
        _ = _ := by ring
    linarith

/-- The manuscript's ratio-five logarithmic endpoint gain, with the entire
positive entropy split and no common child-cap restriction. -/
theorem value_logarithmic_gain {d e f : ℝ}
    (c : PsiEndpointContact.Contact d e f) (hd : 5 * ((e + f) / 2) ≤ d) :
    F d ((e + f) / 2) + d / (2 * Real.log 2) * barrier ((e - f) / (e + f)) ≤ c.value := by
  let E := (e + f) / 2
  let t := (e - f) / (e + f)
  have he := c.entropy_left_pos
  have hf := c.entropy_right_pos
  have hE : 0 < E := by dsimp [E]; linarith
  obtain ⟨cbar⟩ := c.exists_equal_contact
  have hbar : 0 < E / cbar.mass := div_pos hE cbar.mass_pos
  have hbarcap : E / cbar.mass ≤ 19 / 100 := equal_contact_entropy_bound cbar hd
  obtain ⟨ht, het, hft⟩ := PsiRetainedChildBridge.positive_entropy_split he hf
  have hplus : (E / cbar.mass) * (1 + t) = e / cbar.mass := by
    calc
      _ = (E * (1 + t)) / cbar.mass := by ring
      _ = e / cbar.mass := congrArg (fun x => x / cbar.mass) het
  have hminus : (E / cbar.mass) * (1 - t) = f / cbar.mass := by
    calc
      _ = (E * (1 - t)) / cbar.mass := by ring
      _ = f / cbar.mass := congrArg (fun x => x / cbar.mass) hft
  have hgain := Q_split_gain hbar hbarcap ht
  change Q (E / cbar.mass) + barrier t / (2 * Real.log 2) ≤
    (Q ((E / cbar.mass) * (1 + t)) + Q ((E / cbar.mass) * (1 - t))) / 2 at hgain
  rw [hplus, hminus] at hgain
  have hmul := mul_le_mul_of_nonneg_left hgain c.difference_pos.le
  have hlast := c.value_ge_equal_mass_Q cbar (by linarith)
  have hbound : F d E + d / (2 * Real.log 2) * barrier t ≤
      d / 2 * (Q (e / cbar.mass) + Q (f / cbar.mass)) := by
    rw [cbar.F_eq_equal_Q]
    convert! hmul using 1 <;> ring
  exact hbound.trans hlast

/-- Every feasible finite law inherits the ratio-five contact gain through
the proved global supporting plane. -/
theorem law_endpoint_logarithmic_lower {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hd : 5 * μ.meanEntropy ≤ μ.b - μ.a) :
    F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
      barrier ((μ.e - μ.f) / (μ.e + μ.f)) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  obtain ⟨c⟩ := PsiEndpointContact.exists_contact_of_feasible
    ⟨μ.a_interior.1.le, μ.a_interior.2.le⟩
    ⟨μ.b_interior.1.le, μ.b_interior.2.le⟩
    μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap (by linarith : μ.meanEntropy < μ.b - μ.a)
  exact (value_logarithmic_gain c hd).trans (c.value_le_cost μ)

end CKLaneN1c.FiveGain

#print axioms CKLaneN1c.FiveGain.log_37_3_lower
#print axioms CKLaneN1c.FiveGain.entropy_3_40_lower
#print axioms CKLaneN1c.FiveGain.curvature_lower
#print axioms CKLaneN1c.FiveGain.compensated_convexOn
#print axioms CKLaneN1c.FiveGain.Q_split_gain
#print axioms CKLaneN1c.FiveGain.equal_contact_entropy_bound
#print axioms CKLaneN1c.FiveGain.value_logarithmic_gain
#print axioms CKLaneN1c.FiveGain.law_endpoint_logarithmic_lower

end


