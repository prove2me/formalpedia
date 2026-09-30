-- Prove2me | Definitions.Def_CK_GeneralCK_PsiCentralEntropy1024
-- name    : CK_GeneralCK_PsiCentralEntropy1024
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:30:09.795856+00:00
-- url     : https://prove2.me/theorems/75cf08ae-5507-49ee-ba55-dd9c2d584d53
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiCentralEntropy1024` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiCentralEntropy1024` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiCentralEntropy1024` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiCentralEntropy1024 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiCentralEntropy1024.lean)

import Definitions.Def_CK_GeneralCK_PsiOuterEntropy200
import Definitions.Def_CK_GeneralCK_PsiFourRatioBridge
import Definitions.Def_CK_GeneralCK_PsiSmallDistanceLowEntropy

-- ===== source module GeneralCK.PsiCentralEntropy1024 =====
section

/-!
# Opposite active-psi laws through mean entropy 1/1024

The small-distance proof retains the actual child psi profiles, while the
intermediate-distance proof retains their phi profiles and signed entropy
split. Both use established actual-law cost floors.
-/

namespace GeneralCK.PsiCentralEntropy1024
open Set PsiSmallDistance PsiChildEntropyCoupling PsiSignedSplit

theorem neg_deriv_eta_upper {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 960) :
    -deriv eta h ≤ (8 / 5) / h := by
  let v := entropyInverse h
  let t := Real.log ((1 - v) / v)
  have hh1 : h < 1 := by linarith
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hH : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hvc : 0 < 1 - v := by linarith
  have hvsmall : v ≤ 1 / 14000 := by
    have hlog : (27 / 2) * Real.log 2 ≤ Real.log (14000 : ℝ) := by
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ (27 : ℕ))
        (by norm_num : (2 : ℝ) ^ (27 : ℕ) ≤ (14000 : ℝ) ^ (2 : ℕ))
      rw [Real.log_pow, Real.log_pow] at hl
      norm_num at hl
      linarith
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13999 / 14000)
    have hnat : (1 / 14000 : ℝ) * Real.log 14000 +
        (1 / 14000) * (13999 / 14000) ≤ H (1 / 14000) * Real.log 2 := by
      rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
      norm_num
      rw [show (14000 / 13999 : ℝ) = ((13999 / 14000 : ℝ))⁻¹ by norm_num,
        Real.log_inv]
      nlinarith only [hc]
    have hanchor : (1 / 960 : ℝ) ≤ H (1 / 14000) := by
      have hLu : Real.log 2 ≤ (7 / 10 : ℝ) := by
        have hl := Certificates.PilotData.log_two.2
        norm_num at hl
        linarith
      apply (mul_le_mul_iff_right₀ log_two_pos).mp
      nlinarith only [hnat, hlog, hLu]
    by_contra hn
    have hm := H_strictMonoOn (a := (1 / 14000 : ℝ)) (b := v)
      ⟨by norm_num, by norm_num⟩ ⟨hv.le, hvhalf.le⟩ (lt_of_not_ge hn)
    rw [hH] at hm
    linarith
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    have hl := Certificates.PilotData.log_two.1
    norm_num at hl
    linarith
  have ht : 19 / 2 ≤ t := by
    have hratio : (13999 : ℝ) ≤ (1 - v) / v := (le_div_iff₀ hv).2 (by linarith)
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 13999) hratio
    have hp := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ (55 : ℕ))
      (by norm_num : (2 : ℝ) ^ (55 : ℕ) ≤ (13999 : ℝ) ^ (4 : ℕ))
    rw [Real.log_pow, Real.log_pow] at hp
    norm_num at hp
    dsimp [t]
    nlinarith only [hl, hp, hL]
  have htpos : 0 < t := by linarith
  have hlogc : -Real.log (1 - v) ≤ v / (1 - v) := by
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hvc)
    rw [Real.log_inv] at hl
    have heq : (1 - v)⁻¹ - 1 = v / (1 - v) := by field_simp; ring
    rwa [heq] at hl
  have hbin : h * Real.log 2 = v * t - Real.log (1 - v) := by
    rw [← hH, H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
    dsimp [t]
    rw [Real.log_div hvc.ne' hv.ne']
    simp only [Real.log_inv]
    ring
  have hvinv : v / (1 - v) ≤ v * (100 / 99) := by
    apply (div_le_iff₀ hvc).2
    nlinarith [mul_nonneg hv.le (show 0 ≤ 1 / 100 - v by linarith)]
  have hcoef : t + 100 / 99 ≤ (1597 / 1000 : ℝ) * Real.log 2 * t := by
    have hl := mul_le_mul_of_nonneg_right hL htpos.le
    nlinarith only [hl, ht]
  have hhvt : h ≤ (1597 / 1000 : ℝ) * v * t := by
    have hb : h * Real.log 2 ≤ v * (t + 100 / 99) := by nlinarith only [hbin, hlogc, hvinv]
    have hc := mul_le_mul_of_nonneg_left hcoef hv.le
    nlinarith [log_two_pos]
  have hden : 0 < v * (1 - v) * t := by positivity
  have hfrac : h * ((1 - 2 * v) / (v * (1 - v) * t)) ≤ 1597 / 1000 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    have ha := mul_le_mul_of_nonneg_right hhvt hvc.le
    have hb := mul_le_mul_of_nonneg_left (show 1 - 2 * v ≤ 1 - v by linarith) hh.le
    nlinarith only [ha, hb]
  have hd : deriv eta h = -2 - (1 - 2 * v) / (v * (1 - v) * t) := by
    rw [deriv_eta hh hh1]
    change -2 - (1 - 2 * v) / (Real.log 2 * v * (1 - v) * J v) = _
    unfold J
    dsimp [t]
    field_simp
  apply (le_div_iff₀ hh).2
  rw [hd]
  nlinarith only [hfrac, hh']

theorem eta_decrement_upper {E a b : ℝ} (hE : 0 < E)
    (hEa : E ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 960) :
    eta a - eta b ≤ ((8 / 5) / E) * (b - a) := by
  have hm : MonotoneOn (fun h => eta h + ((8 / 5) / E) * h) (Icc E (1 / 960)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun h => deriv eta h + (8 / 5) / E)
    · intro h hh
      exact ((hasDerivAt_eta (by linarith [hh.1]) (by linarith [hh.2])).continuousAt.add
        (continuousAt_id.const_mul _)).continuousWithinAt
    · intro h hh
      have hi := interior_subset hh
      have hd := (hasDerivAt_eta (by linarith [hi.1]) (by linarith [hi.2])).add
        ((hasDerivAt_id h).const_mul ((8 / 5) / E))
      rw [← (hasDerivAt_eta (by linarith [hi.1]) (by linarith [hi.2])).deriv] at hd
      convert! hd.hasDerivWithinAt using 1
      simp
    · intro h hh
      have hi := interior_subset hh
      have hu := neg_deriv_eta_upper (by linarith [hi.1]) hi.2
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8 / 5) hE hi.1
      linarith
  have h := hm ⟨hEa, hab.trans hb⟩ ⟨hEa.trans hab, hb⟩ hab
  linarith

theorem splitBound_le_radial {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hb : 1 / 2 ≤ μ.b)
    (hq : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hE : μ.meanEntropy ≤ 1 / 1024)
    (hd : μ.b - μ.a ≤ 4 * μ.meanEntropy) :
    μ.splitBound ≤ F (μ.b - μ.a) μ.meanEntropy := by
  let q := 1 - μ.a - μ.b
  let d := μ.b - μ.a
  let E := μ.meanEntropy
  have hEpos : 0 < E := by
    dsimp [E, InteriorLaw.meanEntropy]
    linarith [μ.e_pos, μ.f_pos]
  have hdpos : 0 < d := sub_pos.mpr hab
  have hqpos : 0 ≤ q := by dsimp [q]; linarith
  have hqd : q ≤ d := by dsimp [q, d]; linarith
  have hqE : q ≤ 8 * E := hq
  have hdE : d ≤ 4 * E := hd
  have hEi : E ≤ 1 / 1024 := hE
  have hcoords : q - d ∈ Icc (-1 / 128 : ℝ) (1 / 128) ∧
      q + d ∈ Icc (-1 / 128 : ℝ) (1 / 128) := by
    constructor <;> constructor <;> linarith
  have hbound : ∀ r ∈ Icc (-1 / 128 : ℝ) (1 / 128),
      biasDeficit r ≤ (1 / 16384 : ℝ) := by
    intro r hr
    have hc := biasDeficit_le_sq (r := r) (abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    have hs := mul_nonneg (show 0 ≤ r + 1 / 128 by linarith [hr.1])
      (show 0 ≤ 1 / 128 - r by linarith [hr.2])
    nlinarith only [hc, hs]
  have hCp := hbound (q + d) hcoords.2
  have hCm := hbound (q - d) hcoords.1
  have hmid : (1 - q) / 2 = μ.midpoint := by
    dsimp [q, InteriorLaw.midpoint]
    ring
  have hplus : (1 - (q + d)) / 2 = μ.a := by dsimp [q, d]; ring
  have hminus : (1 - (q - d)) / 2 = μ.b := by dsimp [q, d]; ring
  have hparent : 1 - μ.information = E + biasDeficit q := by
    rw [biasDeficit_eq, hmid]
    dsimp [E, InteriorLaw.information]
    ring
  have hchildren : 1 - μ.meanDeficit = E +
      (biasDeficit (q - d) + biasDeficit (q + d)) / 2 := by
    rw [biasDeficit_eq, biasDeficit_eq, hplus, hminus]
    dsimp [E, InteriorLaw.meanEntropy, InteriorLaw.meanDeficit]
    ring
  have harg : E ≤ 1 - μ.information := by
    rw [hparent]
    linarith [biasDeficit_nonneg q]
  have horder : 1 - μ.information ≤ 1 - μ.meanDeficit := by
    linarith [μ.information_eq, μ.entropyDrop_nonneg]
  have hupper : 1 - μ.meanDeficit ≤ (1 / 960 : ℝ) := by
    rw [hchildren]
    linarith only [hCp, hCm, hEi]
  have hinc := deficit_average_increment
    (show q - d ∈ Icc (-1 / 100 : ℝ) (1 / 100) from
      ⟨by linarith [hcoords.1.1], by linarith [hcoords.1.2]⟩)
    (show q + d ∈ Icc (-1 / 100 : ℝ) (1 / 100) from
      ⟨by linarith [hcoords.2.1], by linarith [hcoords.2.2]⟩)
  have hdiff : (1 - μ.meanDeficit) - (1 - μ.information) ≤ (29 / 40) * d ^ 2 := by
    rw [hparent, hchildren]
    linarith only [hinc]
  have heta := eta_decrement_upper hEpos harg horder hupper
  have hmul := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ (8 / 5) / E)
  have hsplit : μ.splitBound = eta (1 - μ.information) - eta (1 - μ.meanDeficit) := by
    unfold InteriorLaw.splitBound
    rw [← μ.information_eq]
    rfl
  have hs : μ.splitBound ≤ (29 / 25) * (d ^ 2 / E) := by
    rw [hsplit]
    calc
      _ ≤ ((8 / 5) / E) * ((1 - μ.meanDeficit) - (1 - μ.information)) := heta
      _ ≤ ((8 / 5) / E) * ((29 / 40) * d ^ 2) := hmul
      _ = _ := by ring
  exact hs.trans (F_lower_small_ratio hdpos hEpos hdE)

/-- The low-distance active-psi branch, for actual finite laws and arbitrary
entropy split. Both children are retained through their psi values. -/
theorem small_distance_law {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hb : 1 / 2 ≤ μ.b)
    (hq : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hE : μ.meanEntropy ≤ 1 / 1024)
    (hd : μ.b - μ.a ≤ 4 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  exact μ.gap_le_of_splitBound hactive
    ((splitBound_le_radial μ hab hsum hb hq hE hd).trans (PsiEndpointPlane.law_radial_lower μ hab))

theorem parent_gain {E q : ℝ} (hE : 0 < E)
    (hEi : E ≤ 1 / 1024) (hq : 0 ≤ q) (hqE : q ≤ 8 * E) :
    (97 / 100) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hgain := PsiLargerEntropyRedesign.parent_gain_rational hE hq (by linarith)
    (PsiLargerEntropyRedesign.parent_entropy_le_one hE (by linarith) hq hqE)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hqSq : q ^ 2 ≤ 64 * E ^ 2 := by nlinarith [sq_nonneg (8 * E - q)]
  have hLE : Real.log 2 * E ≤ (7 / 10 : ℝ) * (1 / 1024) :=
    mul_le_mul hL hEi hE.le (by norm_num)
  have hLsq : (Real.log 2) ^ 2 ≤ (49 / 100 : ℝ) := by nlinarith [log_two_pos]
  have hcoef : 2 * (Real.log 2) ^ 2 + 64 * Real.log 2 * E ≤ 100 / 97 := by nlinarith
  have hden : Real.log 2 * (2 * Real.log 2 * E + q ^ 2) ≤ (100 / 97) * E := by
    have h1 := mul_le_mul_of_nonneg_right hcoef hE.le
    have h2 := mul_le_mul_of_nonneg_left hqSq log_two_pos.le
    nlinarith
  have hb := div_le_div_of_nonneg_left (sq_nonneg q)
    (by positivity : 0 < Real.log 2 * (2 * Real.log 2 * E + q ^ 2)) hden
  have he : q ^ 2 / ((100 / 97) * E) = (97 / 100) * (q ^ 2 / E) := by ring
  rw [he] at hb
  exact hb.trans hgain


theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 1024)
    (hd4 : 4 * E ≤ d) (hd8 : d ≤ 8 * E)
    (hq : 0 ≤ q) (hqd : q ≤ d) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 50) * (q ^ 2 / E) ≤ F d E := by
  have hqE : q ≤ 8 * E := hqd.trans hd8
  have hgain := parent_gain hE hEi hq hqE
  have hr := PsiFourRatioBridge.radial_average_loss hE hd4 q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
  have hr' : radialLoss d q E ≤ (15 / 16) * (q ^ 2 / E) := by
    unfold radialLoss
    linarith only [hr]
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  let c := 1 / (2 * Real.log 2) - 13 * d / 12
  have hc : 1 / 3 ≤ c := by
    have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
      have h := Certificates.PilotData.log_two.2
      norm_num at h
      linarith
    have hbase : (5 / 7 : ℝ) ≤ 1 / (2 * Real.log 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
      linarith
    dsimp [c]
    linarith
  have hs := signed_slope_split_ge_neg_four_sq hc hq (by linarith) hE hA hA' ht
  have hdec := retained_child_decomposition
    (C := 1 - H ((1 - q) / 2)) hq hqd hE (by linarith) ht
  have hcEq : endpointCoefficient d = c + d / (2 * Real.log 2) := by
    dsimp [endpointCoefficient, c]
    ring
  rw [hcEq] at hdec
  have hsmall : 4 * q ^ 2 ≤ (1 / 256) * (q ^ 2 / E) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hE).2
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1 / 256 - 4 * E by linarith)]
  have hn : 0 ≤ q ^ 2 / E := by positivity
  nlinarith only [hgain, hr', hs, hdec, hsmall, hn]

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b)
    (hEi : μ.meanEntropy ≤ 1 / 1024)
    (hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hd8 : μ.b - μ.a ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hq : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := by linarith
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hc := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq hqd (by rwa [hmean])
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rw [hca, hcb, hce, hcf] at hc
  change μ.gap ≤ _ at hc
  have h := retained_child_margin hE hEi hd4 hd8 hq hqd ht
  have hcost := PsiEndpointPlane.law_radial_lower μ (by linarith)
  linarith only [hc, h, hcost]

theorem intermediate_distance_law {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hside : 1 / 2 ≤ μ.b)
    (hEi : μ.meanEntropy ≤ 1 / 1024)
    (hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hd8 : μ.b - μ.a ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (1 / 50) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  have h := law_gap_margin μ hsum hside hEi hd4 hd8 hactive
  linarith only [h, hm]

/-- The complete opposite chart, including arbitrary child entropy splits
and all mean separations, is closed through the stated entropy ceiling. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hEi : μ.meanEntropy ≤ 1 / 1024)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have heq : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hq := PsiOuterEntropy200.active_bias_lt_eight_entropy
    (q := 1 - μ.a - μ.b)
    (by linarith [μ.a_interior.1]) hE (by linarith) (by rwa [heq])
  by_cases h4 : μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact small_distance_law μ hab hsum hb hq.le hEi h4 hactive
  · by_cases h8 : μ.b - μ.a ≤ 8 * μ.meanEntropy
    · exact intermediate_distance_law μ hsum hb hEi (lt_of_not_ge h4).le h8 hactive
    · exact PsiModerateEntropy.law_gap_le_cost_ceiling μ hsum (by linarith)
        (lt_of_not_ge h8).le (by linarith) hactive

end GeneralCK.PsiCentralEntropy1024

#print axioms GeneralCK.PsiCentralEntropy1024.neg_deriv_eta_upper
#print axioms GeneralCK.PsiCentralEntropy1024.small_distance_law

#print axioms GeneralCK.PsiCentralEntropy1024.parent_gain
#print axioms GeneralCK.PsiCentralEntropy1024.intermediate_distance_law
#print axioms GeneralCK.PsiCentralEntropy1024.law_gap_le_cost

end


