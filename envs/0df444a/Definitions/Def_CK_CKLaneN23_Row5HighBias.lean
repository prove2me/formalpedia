-- Prove2me | Definitions.Def_CK_CKLaneN23_Row5HighBias
-- name    : CK_CKLaneN23_Row5HighBias
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:12:21.810329+00:00
-- url     : https://prove2.me/theorems/a7031a3e-94e2-4f81-8237-ccb8031bd5e7
-- title:
--   Courtade–Kumar proof module `CKLaneN23.Row5HighBias` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.Row5HighBias` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.Row5HighBias` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.Row5HighBias (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/Row5HighBias.lean)

import Definitions.Def_CK_CKLaneN23_SameSideHalf
import Definitions.Def_CK_GeneralCK_PsiBoundaryLeafReplay
import Definitions.Def_CK_GeneralCK_PsiSmallDistanceLowEntropy
import Definitions.Def_CK_GeneralCK_PsiFourRatioBridge

-- ===== source module CKLaneN23.Row5HighBias =====
section

/-!
# Lane N23 — row 5 `NoSepA_HighBiasRem` (NO_SEPARATION §5 on `q > 1/2`)

Row 5 of `CKLaneN23.sameSideHalf_of_certificate_rows`: central means, `d ≤ 1/50`,
`4E ≤ d`, `q > 1/2`, `E > 10^-6`, strict psi-activity `⟹ gap ≤ cost`.

Archived argument (NO_SEPARATION §5): the psi split is bounded by the entropy Jensen gap
times the slope of `P(t) = η(1-t)`,
`R_ψ ≤ P(I) - P(s) ≤ Δ·P'`, with the curvature bound `Δ ≤ d²/(2L(1-(q+d)²))` (13), while
`ζ ≥ F(d,E)` and the radial profile bounds `F(d,E)` below by a multiple of `d`. On the
remaining range `q ∈ (1/2, 4/5]` one coarse comparison suffices (it replaces the archived
comparisons `k = 5,6,7`):

* `Δ ≤ (21/10) d²` (concavity of `C(r) - (21/10) r²` on `|r| ≤ 4/5`);
* `P(I) - P(s) ≤ Δ · 20(η(1/20) - η(1/10)) ≤ Δ · 4692/100` (convexity of `P`, `I ≤ 9/10`,
  rational entropy-inverse witnesses `1/200`, `1/50`);
* `F(d,E) ≥ (39/10) d` for `d ≥ 4E` (contact below `1/16`, `J(1/16) ≥ 39/10`);
* `(21/10)·(4692/100)·d² ≤ (21/10)·(4692/100)·d/50 ≤ (39/10) d`.

Everything else is reused from compiled F-C theorems: `InteriorLaw.gap_le_of_splitBound`,
`Scalar.P_convexOn`, `PsiEndpointPlane.law_radial_lower` (`ζ ≥ F(d,E)`), the contact and
entropy-inverse calculus, and the rational `log₂` power witnesses of `BoundaryStrip`.
-/

namespace CKLaneN23.Row5

open GeneralCK Set

/-! ## Scalar facts -/

theorem log_two_bounds :
    (34657359 / 50000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 693147181 / 1000000000 := by
  have h := Certificates.PilotData.log_two
  norm_num at h
  exact h

/-- `p log(1/p) + p(1-p) ≤ H(p) log 2`. -/
theorem entropy_natural_lower {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) :
    p * Real.log p⁻¹ + p * (1 - p) ≤ H p * Real.log 2 := by
  have hc : 0 < 1 - p := by linarith
  have h := Real.log_le_sub_one_of_pos hc
  have hl : p ≤ Real.log (1 - p)⁻¹ := by rw [Real.log_inv]; linarith
  have hh := mul_le_mul_of_nonneg_left hl hc.le
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
  nlinarith

theorem H_one_sixteenth : (1 / 4 : ℝ) ≤ H (1 / 16) := by
  have h := entropy_natural_lower (p := 1 / 16) (by norm_num) (by norm_num)
  have hlog : Real.log ((1 / 16 : ℝ)⁻¹) = 4 * Real.log 2 := by
    rw [show ((1 / 16 : ℝ)⁻¹) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog] at h
  have hL := log_two_pos
  by_contra hn
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hL
  nlinarith

theorem H_one_fiftieth : (1 / 10 : ℝ) ≤ H (1 / 50) := by
  have h := entropy_natural_lower (p := 1 / 50) (by norm_num) (by norm_num)
  have hlog : 5 * Real.log 2 ≤ Real.log ((1 / 50 : ℝ)⁻¹) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 32) (by norm_num : (32 : ℝ) ≤ 50)
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow] at hl
    norm_num at hl ⊢
    exact hl
  have hL := log_two_pos
  by_contra hn
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hL
  nlinarith

theorem H_one_two_hundredth : H (1 / 200) ≤ 1 / 20 :=
  BoundaryStrip.H_le_of_pow (v := 1 / 200) (b := 200) (p := 39) (k := 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem H_one_quarter : H (1 / 4) ≤ 9 / 10 :=
  BoundaryStrip.H_le_of_pow (v := 1 / 4) (b := 4) (p := 2) (k := 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem J_one_two_hundredth : J (1 / 200) ≤ 39 / 5 :=
  BoundaryStrip.J_le_of_pow (v := 1 / 200) (b := 199) (p := 39) (k := 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem J_one_fiftieth : 28 / 5 ≤ J (1 / 50) :=
  BoundaryStrip.le_J_of_pow (u := 1 / 50) (b := 49) (c := 1) (p := 28) (k := 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem J_one_sixteenth : 39 / 10 ≤ J (1 / 16) :=
  BoundaryStrip.le_J_of_pow (u := 1 / 16) (b := 15) (c := 1) (p := 39) (k := 10) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Lower bound on `η` from an entropy-inverse witness (mirror of `eta_le_of_H_le`). -/
theorem le_eta_of_le_H {h v : ℝ} (hv0 : 0 < v) (hvh : v ≤ 1 / 2) (hh0 : 0 < h)
    (hHv : h ≤ H v) : (1 - 2 * v) * J v ≤ eta h := by
  have hv1 : v < 1 := lt_of_le_of_lt hvh (by norm_num)
  have hHpos : 0 < H v := H_pos hv0 hv1
  have key := eta_antitoneOn (Set.mem_Ioc.2 ⟨hh0, hHv.trans (H_le_one v)⟩)
    (Set.mem_Ioc.2 ⟨hHpos, H_le_one v⟩) hHv
  rwa [eta_eq_profile hHpos.le (H_le_one v), entropyInverse_H_lower hv0.le hvh] at key

theorem eta_one_twentieth : eta (1 / 20) ≤ (99 / 100) * (39 / 5) := by
  have h := BoundaryStrip.eta_le_of_H_le (h := 1 / 20) (v := 1 / 200) (by norm_num)
    (by norm_num) (by norm_num) H_one_two_hundredth
  have hJ := J_one_two_hundredth
  norm_num at h ⊢
  linarith

theorem eta_one_tenth : (24 / 25) * (28 / 5) ≤ eta (1 / 10) := by
  have h := le_eta_of_le_H (h := 1 / 10) (v := 1 / 50) (by norm_num) (by norm_num)
    (by norm_num) H_one_fiftieth
  have hJ := J_one_fiftieth
  norm_num at h ⊢
  linarith

/-! ## The entropy second difference on `|r| ≤ 4/5` -/

theorem deficit_concave_wide :
    ConcaveOn ℝ (Icc (-4 / 5) (4 / 5))
      (fun r => PsiSmallDistance.biasDeficit r - (21 / 10) * r ^ 2) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun r => SmallMean.A r / Real.log 2 - (21 / 5) * r)
    (f'' := fun r => 1 / (Real.log 2 * (1 - r ^ 2)) - 21 / 5)
  · exact (SmallMean.Cn_continuous.div_const (Real.log 2)).continuousOn.sub
      ((continuous_id.pow 2).const_mul (21 / 10)).continuousOn
  · intro r hr
    have hi := interior_subset hr
    have hd := ((SmallMean.hasDerivAt_Cn (by linarith [hi.1]) (by linarith [hi.2])).div_const
      (Real.log 2)).sub (((hasDerivAt_id r).pow 2).const_mul (21 / 10))
    convert! hd.hasDerivWithinAt using 1 <;> simp <;> ring
  · intro r hr
    have hi := interior_subset hr
    have hd := ((SmallMean.hasDerivAt_A (by linarith [hi.1]) (by linarith [hi.2])).div_const
      (Real.log 2)).sub ((hasDerivAt_id r).const_mul (21 / 5))
    convert! hd.hasDerivWithinAt using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro r hr
    have hi := interior_subset hr
    have hs : r ^ 2 ≤ (16 / 25 : ℝ) := by
      nlinarith [mul_nonneg (show 0 ≤ r + 4 / 5 by linarith [hi.1])
        (show 0 ≤ 4 / 5 - r by linarith [hi.2])]
    have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
      have hl := log_two_bounds.1
      linarith
    have hden : 0 < Real.log 2 * (1 - r ^ 2) := mul_pos log_two_pos (by linarith)
    have hb := mul_le_mul hL (show (9 / 25 : ℝ) ≤ 1 - r ^ 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 9 / 25) log_two_pos.le
    have hf : 1 / (Real.log 2 * (1 - r ^ 2)) ≤ (21 / 5 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith only [hb]
    linarith

theorem deficit_second_difference {q d : ℝ} (hp : q + d ∈ Icc (-4 / 5 : ℝ) (4 / 5))
    (hm : q - d ∈ Icc (-4 / 5 : ℝ) (4 / 5)) :
    (PsiSmallDistance.biasDeficit (q + d) + PsiSmallDistance.biasDeficit (q - d)) / 2 -
      PsiSmallDistance.biasDeficit q ≤ (21 / 10) * d ^ 2 := by
  have hj := deficit_concave_wide.2 hm hp
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hj
  rw [show (1 / 2 : ℝ) * (q - d) + (1 / 2) * (q + d) = q by ring] at hj
  nlinarith only [hj]

theorem biasDeficit_mono {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ ≤ 1) :
    PsiSmallDistance.biasDeficit r₁ ≤ PsiSmallDistance.biasDeficit r₂ := by
  rw [PsiSmallDistance.biasDeficit_eq, PsiSmallDistance.biasDeficit_eq]
  have hm := H_strictMonoOn.monotoneOn
    (show (1 - r₂) / 2 ∈ Icc (0 : ℝ) (1 / 2) by constructor <;> linarith)
    (show (1 - r₁) / 2 ∈ Icc (0 : ℝ) (1 / 2) by constructor <;> linarith) (by linarith)
  linarith

/-! ## Convex secant comparison -/

theorem convex_increment_le {f : ℝ → ℝ} {S : Set ℝ} (hf : ConvexOn ℝ S f) {x y u v : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxy : x ≤ y) (hyv : y < v) (hxu : x ≤ u) (huv : u < v) :
    f y - f x ≤ (y - x) * ((f v - f u) / (v - u)) := by
  rcases hxy.eq_or_lt with heq | hlt
  · rw [heq]; simp
  have h1 : (f y - f x) / (y - x) ≤ (f v - f x) / (v - x) :=
    hf.secant_mono hx hy hv hlt.ne' (ne_of_gt (show x < v by linarith)) hyv.le
  have h2 : (f x - f v) / (x - v) ≤ (f u - f v) / (u - v) :=
    hf.secant_mono hv hx hu (ne_of_lt (show x < v by linarith)) huv.ne hxu
  have e1 : (f v - f x) / (v - x) = (f x - f v) / (x - v) := by
    rw [show f v - f x = -(f x - f v) by ring, show v - x = -(x - v) by ring, neg_div_neg_eq]
  have e2 : (f u - f v) / (u - v) = (f v - f u) / (v - u) := by
    rw [show f u - f v = -(f v - f u) by ring, show u - v = -(v - u) by ring, neg_div_neg_eq]
  have hslope : (f y - f x) / (y - x) ≤ (f v - f u) / (v - u) := by
    rw [← e2]; rw [e1] at h1; exact h1.trans h2
  have hpos : 0 < y - x := by linarith
  have := mul_le_mul_of_nonneg_left hslope hpos.le
  rwa [mul_div_cancel₀ _ hpos.ne'] at this

/-! ## The `§5` split bound on `q > 1/2` -/

theorem slope_P_le :
    (Scalar.P (19 / 20) - Scalar.P (9 / 10)) / (19 / 20 - 9 / 10) ≤ 4692 / 100 := by
  have h1 := eta_one_twentieth
  have h2 := eta_one_tenth
  have e1 : Scalar.P (19 / 20) = eta (1 / 20) := by unfold Scalar.P; norm_num
  have e2 : Scalar.P (9 / 10) = eta (1 / 10) := by unfold Scalar.P; norm_num
  rw [e1, e2]
  norm_num at h1 h2 ⊢
  linarith

theorem entropyDrop_eq {k : ℕ} (μ : InteriorLaw (Fin k)) :
    μ.entropyDrop =
      (PsiSmallDistance.biasDeficit ((1 - μ.a - μ.b) + (μ.b - μ.a)) +
        PsiSmallDistance.biasDeficit ((1 - μ.a - μ.b) - (μ.b - μ.a))) / 2 -
        PsiSmallDistance.biasDeficit (1 - μ.a - μ.b) := by
  rw [PsiSmallDistance.biasDeficit_eq, PsiSmallDistance.biasDeficit_eq,
    PsiSmallDistance.biasDeficit_eq]
  have e1 : (1 - ((1 - μ.a - μ.b) + (μ.b - μ.a))) / 2 = μ.a := by ring
  have e2 : (1 - ((1 - μ.a - μ.b) - (μ.b - μ.a))) / 2 = μ.b := by ring
  have e3 : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  rw [e1, e2, e3]
  unfold InteriorLaw.entropyDrop
  ring

theorem information_eq_bias {k : ℕ} (μ : InteriorLaw (Fin k)) :
    μ.information = 1 - PsiSmallDistance.biasDeficit (1 - μ.a - μ.b) - μ.meanEntropy := by
  rw [PsiSmallDistance.biasDeficit_eq]
  have e3 : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint; ring
  rw [e3]
  unfold InteriorLaw.information
  ring

theorem splitBound_le_highBias {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b)
    (ha : 1 / 10 ≤ μ.a) (hd : μ.b - μ.a ≤ 1 / 50) (hq : 1 / 2 < 1 - μ.a - μ.b) :
    μ.splitBound ≤ (39 / 10) * (μ.b - μ.a) := by
  have hE := meanEntropy_pos' μ
  have hΔ0 := μ.entropyDrop_nonneg
  have hs := μ.meanDeficit_mem
  have hΔ : μ.entropyDrop ≤ (21 / 10) * (μ.b - μ.a) ^ 2 := by
    rw [entropyDrop_eq]
    exact deficit_second_difference (by constructor <;> linarith) (by constructor <;> linarith)
  have hC : (1 / 10 : ℝ) ≤ PsiSmallDistance.biasDeficit (1 - μ.a - μ.b) := by
    have hm := biasDeficit_mono (r₁ := 1 / 2) (r₂ := 1 - μ.a - μ.b) (by norm_num) hq.le
      (by linarith)
    have hh : PsiSmallDistance.biasDeficit (1 / 2) = 1 - H (1 / 4) := by
      rw [PsiSmallDistance.biasDeficit_eq]; norm_num
    have hq4 := H_one_quarter
    linarith
  have hI : μ.entropyDrop + μ.meanDeficit ≤ 9 / 10 := by
    rw [← μ.information_eq, information_eq_bias]
    linarith
  have hslope := convex_increment_le Scalar.P_convexOn
    (x := μ.meanDeficit) (y := μ.entropyDrop + μ.meanDeficit) (u := 9 / 10) (v := 19 / 20)
    ⟨hs.1, hs.2⟩ ⟨by linarith [hs.1], by linarith⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by linarith) (by linarith) (by linarith) (by norm_num)
  have hS := slope_P_le
  have hsplit : μ.splitBound =
      Scalar.P (μ.entropyDrop + μ.meanDeficit) - Scalar.P μ.meanDeficit := rfl
  rw [hsplit]
  have hd0 : 0 ≤ μ.b - μ.a := by linarith
  have hdd : (μ.b - μ.a) ^ 2 ≤ (1 / 50) * (μ.b - μ.a) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hS hΔ0
  have e : μ.entropyDrop + μ.meanDeficit - μ.meanDeficit = μ.entropyDrop := by ring
  rw [e] at hslope
  nlinarith

/-! ## Radial lower bound `F(d,E) ≥ (39/10) d` for `d ≥ 4E` -/

theorem F_lower_ratio_four {d E : ℝ} (hE : 0 < E) (hd4 : 4 * E ≤ d) :
    (39 / 10) * d ≤ F d E := by
  have hd : 0 < d := by linarith
  have hcont : radialContact d E ≤ 1 / 16 := by
    rw [radialContact_le_iff hd hE (by norm_num) (by norm_num)]
    have hH := H_one_sixteenth
    nlinarith
  have hpos := radialContact_pos hd hE
  have hJ : J (1 / 16) ≤ J (radialContact d E) := J_antitone hpos (by norm_num) hcont
  have hJ16 := J_one_sixteenth
  rw [F, if_neg hd.ne']
  nlinarith

/-! ## Row 5 -/

/-- Row 5 of `sameSideHalf_of_certificate_rows`, unconditionally. -/
theorem row_noSepA_highBiasRem : NoSepA_HighBiasRem := by
  intro k μ hab _hsum ha _hb hd _hEu hd4 hq _hEl hact
  have hE := meanEntropy_pos' μ
  have hab' : μ.a < μ.b := by linarith
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  apply μ.gap_le_of_splitBound hact'.le
  have hcost := PsiEndpointPlane.law_radial_lower μ hab'
  have hF := F_lower_ratio_four hE hd4
  have hs := splitBound_le_highBias μ hab ha hd hq
  linarith

end CKLaneN23.Row5

end


