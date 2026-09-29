-- Prove2me | Definitions.Def_CK_GeneralCK_PsiLowEntropyRedesign
-- name    : CK_GeneralCK_PsiLowEntropyRedesign
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:12:09.370801+00:00
-- url     : https://prove2.me/theorems/ecccb372-4f0b-405f-b75f-2357127f3d67
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiLowEntropyRedesign` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiLowEntropyRedesign` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiLowEntropyRedesign` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiLowEntropyRedesign (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiLowEntropyRedesign.lean)

import Definitions.Def_CK_GeneralCK_PsiParentEntropyGain
import Definitions.Def_CK_GeneralCK_PsiRadialDeficit
import Definitions.Def_CK_GeneralCK_PsiChildEntropyCoupling
import Definitions.Def_CK_GeneralCK_PsiSplitLossBound
import Definitions.Def_CK_GeneralCK_PsiEntropySlopeVariation
import Definitions.Def_CK_GeneralCK_PsiRetainedChildBridge_v2

-- ===== source module GeneralCK.PsiLowEntropyRedesign =====
section

/-!
# Analytic low-entropy replacement for the refuted active-psi shortcut

This proves the retained two-child comparison with the explicit endpoint
expression. The nonnegative margin is uniform in the entire open entropy split
interval, and is strictly positive when q is positive. It is not a proof that this endpoint expression bounds every
finite law's cost; that is a separate remaining theorem.
-/

namespace GeneralCK.PsiLowEntropyRedesign
open PsiChildEntropyCoupling PsiSignedSplit

theorem parent_entropy_le_one {E q : ℝ} (hE : 0 < E)
    (hEi : E ≤ 1 / 1000000) (hq : 0 ≤ q) (hqE : q ≤ 8 * E) :
    E + (1 - H ((1 - q) / 2)) ≤ 1 := by
  rcases hq.eq_or_lt with he | hp
  · rw [← he]
    norm_num [H_half]
    linarith
  · have hq1 : q < 1 := by linarith
    have hh := H_gt_parabola (p := (1 - q) / 2) (by linarith) (by linarith)
    have hsmall := mul_nonneg hq (show 0 ≤ 1 / 100 - q by linarith)
    nlinarith

theorem child_slope_bounds {d q E : ℝ} (hE : 0 < E) (hE1 : E < 1)
    (hq : 0 ≤ q) (hqd : q ≤ d) :
    0 ≤ slopeDifference d q E ∧ slopeDifference d q E ≤ 13 * q / (3 * E) := by
  have h := PsiEntropySlopeVariation.radialPhi_entropySlope_variation
    (r0 := d - q) (r1 := d + q) hE hE1 (by linarith) (by linarith)
  refine ⟨h.1, ?_⟩
  convert! h.2 using 1
  ring

/-- A fully analytic comparison with margin `49*q^2/(100*E)`. All entropy
allocations with positive children are included, as are `q=0` and `d=q`.
No feasible-cap or endpoint-cost hypothesis is assumed. -/
theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 1000000)
    (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (49 / 100) * (q ^ 2 / E) ≤
      F d E + d / (2 * Real.log 2) * barrier t := by
  have hqd : q ≤ d := hqE.trans hd
  have hgain := eta_parent_gain_small_entropy hE hEi hq hqE
    (parent_entropy_le_one hE hEi hq hqE)
  have hrad := PsiRadialDeficit.radial_average_loss_le_half hE hd q
  rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
    abs_of_nonneg (show 0 ≤ d + q by linarith)] at hrad
  have hrad' : radialLoss d q E ≤ q ^ 2 / (2 * E) := by
    unfold radialLoss
    linarith only [hrad]
  obtain ⟨hA, hA'⟩ := child_slope_bounds hE (by linarith) hq hqd
  have hc : 1 / 3 ≤ endpointCoefficient d :=
    endpoint_coefficient_ge_third (by linarith) hd1
  have hsplit := signed_slope_split_ge_neg_four_sq hc hq (by linarith) hE hA hA' ht
  have hdec := retained_child_decomposition
    (C := 1 - H ((1 - q) / 2)) hq hqd hE (by linarith) ht
  have hsmall : 4 * q ^ 2 ≤ (1 / 100) * (q ^ 2 / E) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hE).mpr
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1 / 100 - 4 * E by linarith)]
  have he : q ^ 2 / (2 * E) = (q ^ 2 / E) / 2 := by ring
  rw [he] at hrad'
  linarith

/-- The margin now applies to the actual hybrid Bellman gap. Child maxima
are retained by the branch comparison, not assumed to choose either branch. -/
theorem canonical_hybrid_gap_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 1000000)
    (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) :
    candidateGap B ((1 - d - q) / 2) ((1 + d - q) / 2)
      (E * (1 + t)) (E * (1 - t)) + (49 / 100) * (q ^ 2 / E) ≤
      F d E + d / (2 * Real.log 2) * barrier t := by
  have h := retained_child_margin hE hEi hd hd1 hq hqE ht
  have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (t := t) hq (hqE.trans hd) hactive
  linarith

/-- The same result in original means and child entropies, with the chart
identities and signed split derived rather than assumed. -/
theorem opposite_hybrid_gap_margin {a b e f : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hsum : a + b ≤ 1)
    (he : 0 < e) (hf : 0 < f) (hEi : (e + f) / 2 ≤ 1 / 1000000)
    (hd : 8 * ((e + f) / 2) ≤ b - a)
    (hqE : 1 - a - b ≤ 8 * ((e + f) / 2))
    (hactive : phi ((a + b) / 2) ((e + f) / 2) ≤
      psi ((a + b) / 2) ((e + f) / 2)) :
    candidateGap B a b e f + (49 / 100) * ((1 - a - b) ^ 2 / ((e + f) / 2)) ≤
      F (b - a) ((e + f) / 2) + (b - a) / (2 * Real.log 2) *
        barrier ((e - f) / (e + f)) := by
  have hmean : (1 - (1 - a - b)) / 2 = (a + b) / 2 := by ring
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split he hf
  have h := canonical_hybrid_gap_margin
    (d := b - a) (q := 1 - a - b) (E := (e + f) / 2)
    (t := (e - f) / (e + f)) (by linarith) hEi hd (by linarith)
    (by linarith) hqE ht (by rwa [hmean])
  have hca : (1 - (b - a) - (1 - a - b)) / 2 = a := by ring
  have hcb : (1 + (b - a) - (1 - a - b)) / 2 = b := by ring
  rwa [hca, hcb, hce, hcf] at h

/-- A theorem for actual finite laws, still comparing with the explicit
endpoint expression. This is unconditional on any endpoint supporting plane. -/
theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (49 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤
      F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
        barrier ((μ.e - μ.f) / (μ.e + μ.f)) :=
  opposite_hybrid_gap_margin μ.a_interior.1.le μ.b_interior.2.le hsum
    μ.e_pos μ.f_pos hEi hd hqE hactive

/-- Explicit remaining dependency: a future endpoint cost theorem will
close this branch immediately. This theorem does not assert that input. -/
theorem law_gap_le_cost_of_endpoint_lower {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 1000000)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy)
    (hendpoint : F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
      barrier ((μ.e - μ.f) / (μ.e + μ.f)) ≤ μ.cost) : μ.gap ≤ μ.cost := by
  have h := law_gap_margin μ hsum hEi hd hqE hactive
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hp : 0 ≤ (49 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith

end GeneralCK.PsiLowEntropyRedesign

#print axioms GeneralCK.PsiLowEntropyRedesign.retained_child_margin
#print axioms GeneralCK.PsiLowEntropyRedesign.canonical_hybrid_gap_margin
#print axioms GeneralCK.PsiLowEntropyRedesign.law_gap_margin
#print axioms GeneralCK.PsiLowEntropyRedesign.law_gap_le_cost_of_endpoint_lower

end


