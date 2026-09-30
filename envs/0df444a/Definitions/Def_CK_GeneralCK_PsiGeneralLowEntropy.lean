-- Prove2me | Definitions.Def_CK_GeneralCK_PsiGeneralLowEntropy
-- name    : CK_GeneralCK_PsiGeneralLowEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:07:26.946979+00:00
-- url     : https://prove2.me/theorems/c8a4bf7b-7fd5-42c7-bfac-d504281c2321
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiGeneralLowEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiGeneralLowEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiGeneralLowEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiGeneralLowEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiGeneralLowEntropy.lean)

import Definitions.Def_CK_GeneralCK_PsiFourRatioBridge
import Definitions.Def_CK_GeneralCK_PsiSmallDistanceLowEntropy
import Definitions.Def_CK_GeneralCK_PsiLowEntropyBias
import Definitions.Def_CK_GeneralCK_PsiEndpointBellman

-- ===== source module GeneralCK.PsiGeneralLowEntropy =====
section

/-!
# Low entropy without a restriction on which side contains the children

For same-side means the two nonnegative child radii have center `q` and
displacement `d`. Swapping these two arguments in the existing entropy
comparison preserves the sharp radial-loss estimate centered at `d`.
-/

namespace GeneralCK.PsiGeneralLowEntropy
open Set PsiChildEntropyCoupling PsiSignedSplit PsiExtendedEntropyCurvature

theorem sameSide_retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 1000000)
    (hd4 : 4 * E ≤ d) (hdq : d ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage q d E t +
      (1 / 20) * (q ^ 2 / E) ≤ F d E := by
  have hd : 0 ≤ d := by linarith
  have hq : 0 ≤ q := hd.trans hdq
  have hgain := eta_parent_gain_small_entropy hE hEi hq hqE
    (PsiLowEntropyRedesign.parent_entropy_le_one hE hEi hq hqE)
  have hr := PsiFourRatioBridge.radial_average_loss hE hd4 q
  rw [abs_sub_comm d q, abs_of_nonneg (sub_nonneg.mpr hdq),
    abs_of_nonneg (show 0 ≤ d + q by linarith), add_comm d q] at hr
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hd hdq
  let c := 1 / (2 * Real.log 2) - 13 * q / 12
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
  have hs := signed_slope_split_ge_neg_four_sq hc hd (by linarith) hE hA hA' ht
  have hchild := child_average_lower hd hdq hE (by linarith) ht
  have hcomp : compensation q = 2 * c := by dsimp [compensation, c]; ring
  rw [hcomp] at hchild
  unfold radialPhi at hchild
  have hsmall : 4 * d ^ 2 ≤ (1 / 100) * (q ^ 2 / E) := by
    have hsq : d ^ 2 ≤ q ^ 2 := sq_le_sq₀ hd hq |>.2 hdq
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hE).2
    have hEbound := mul_le_mul_of_nonneg_left hEi (sq_nonneg q)
    have hh := mul_le_mul_of_nonneg_right hsq hE.le
    nlinarith only [hEbound, hh, sq_nonneg q]
  have hn : 0 ≤ q ^ 2 / E := by positivity
  nlinarith only [hgain, hr, hs, hchild, hsmall, hn]

theorem sameSide_law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hside : μ.b ≤ 1 / 2)
    (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 20) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  let d := μ.b - μ.a
  let q := 1 - μ.a - μ.b
  let E := μ.meanEntropy
  let t := (μ.e - μ.f) / (μ.e + μ.f)
  have hE : 0 < E := by
    dsimp [E, InteriorLaw.meanEntropy]
    linarith [μ.e_pos, μ.f_pos]
  have hd : 0 ≤ d := (sub_pos.mpr hab).le
  have hdq : d ≤ q := by dsimp [d, q]; linarith
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  change E * (1 + t) = μ.e at hce
  change E * (1 - t) = μ.f at hcf
  have hra : |1 - 2 * μ.a| = q + d := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * μ.a)]
    dsimp [q, d]
    ring
  have hrb : |1 - 2 * μ.b| = q - d := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * μ.b)]
    dsimp [q, d]
    ring
  have hchildren : (phi μ.a μ.e + phi μ.b μ.f) / 2 = childAverage q d E t := by
    unfold phi childAverage radialPhi
    rw [hra, hrb, hce, hcf]
  have hmean : (1 - q) / 2 = μ.midpoint := by dsimp [q, InteriorLaw.midpoint]; ring
  have hparent : psi μ.midpoint μ.meanEntropy = eta (E + (1 - H ((1 - q) / 2))) := by
    rw [hmean]
    unfold psi
    dsimp [E]
    congr 1
    ring
  have hgap := PsiRetainedChildBridge.hybrid_gap_le_retained_phi hactive
  change μ.gap ≤ psi μ.midpoint μ.meanEntropy - (phi μ.a μ.e + phi μ.b μ.f) / 2 at hgap
  rw [hchildren, hparent] at hgap
  have hmargin := sameSide_retained_child_margin hE hEi hd4 hdq hqE ht
  have hcost := PsiEndpointPlane.law_radial_lower μ hab
  change F d E ≤ μ.cost at hcost
  change μ.gap + (1 / 20) * (q ^ 2 / E) ≤ μ.cost
  linarith only [hgap, hmargin, hcost]

theorem sameSide_law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hside : μ.b ≤ 1 / 2)
    (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hd4 : 4 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (1 / 20) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [sameSide_law_gap_margin μ hab hsum hside hEi hd4 hqE hactive, hm]

/-- Every canonical low-entropy active-psi law above the already covered
mean tail, including same-side means and parent ties. -/
theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1) (hmean : 1 / 16 < μ.a + μ.b)
    (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hqi : 1 - μ.a - μ.b ≤ 15 / 16 := by linarith
  have hmean' : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hactive' : phi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy ≤
      psi ((1 - (1 - μ.a - μ.b)) / 2) μ.meanEntropy := by rwa [hmean']
  have hq := PsiLowEntropyBias.active_bias_lt_eight_entropy hqi hE hEi hactive'
  have hqt := PsiLowEntropyBias.active_bias_lt_tenth hqi hE hEi hactive'
  by_cases h4 : μ.b - μ.a ≤ 4 * μ.meanEntropy
  · exact PsiSmallDistance.law_gap_le_cost μ hab hsum hq.le hEi h4 hactive
  · by_cases h8 : μ.b - μ.a ≤ 8 * μ.meanEntropy
    · by_cases hside : μ.b ≤ 1 / 2
      · exact sameSide_law_gap_le_cost μ hab hsum hside hEi (lt_of_not_ge h4).le hq.le hactive
      · exact PsiFourRatioBridge.law_gap_le_cost μ hsum (lt_of_not_ge hside).le
          hEi (lt_of_not_ge h4).le h8 hactive
    · exact PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith)
        (lt_of_not_ge h8).le hqt.le hactive

end GeneralCK.PsiGeneralLowEntropy

#print axioms GeneralCK.PsiGeneralLowEntropy.sameSide_retained_child_margin
#print axioms GeneralCK.PsiGeneralLowEntropy.sameSide_law_gap_margin
#print axioms GeneralCK.PsiGeneralLowEntropy.law_gap_le_cost

end


