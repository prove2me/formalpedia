-- Prove2me | Definitions.Def_CK_GeneralCK_SmallMeanRegion
-- name    : CK_GeneralCK_SmallMeanRegion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:37:51.510051+00:00
-- url     : https://prove2.me/theorems/fd8a7d0f-2d55-42af-9d46-e32c1f48bc88
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallMeanRegion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallMeanRegion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallMeanRegion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallMeanRegion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallMeanRegion.lean)

import Definitions.Def_CK_GeneralCK_SmallMeanEndpoint
import Definitions.Def_CK_GeneralCK_SmallMeanMeans
import Definitions.Def_CK_GeneralCK_ScalarGap
import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_LogSum
import Definitions.Def_CK_GeneralCK_DeterministicCap

namespace GeneralCK

/-- The complete small-mean estimate for the split-uniform psi comparison.
All twenty numerical leaves and every analytic input are discharged. -/
theorem small_mean_splitBound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsmall : μ.a+μ.b ≤ 1/16) : μ.splitBound ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hab'
  · have hD : μ.entropyDrop = 0 := by
      unfold InteriorLaw.entropyDrop InteriorLaw.midpoint
      rw [← heq, show (μ.a+μ.a)/2 = μ.a by ring]
      ring
    have hc : 0 ≤ μ.cost := by
      simpa [← heq, interiorCost] using LogSum.cost_lower_bound μ
    simpa only [InteriorLaw.splitBound,hD,zero_add,sub_self] using hc
  let t := H μ.midpoint
  let D := μ.entropyDrop
  let S := (H μ.a+H μ.b)/2
  let r := (μ.b-μ.a)/(μ.a+μ.b)
  let j := interiorCost μ.a μ.b
  let α := (μ.b-μ.a)^2/(2*μ.b*(1-μ.a))
  let s := μ.meanDeficit
  have hm0 : 0 < μ.midpoint := by
    have h₁ := μ.a_interior.1
    have h₂ := μ.b_interior.1
    unfold InteriorLaw.midpoint; linarith
  have hm1 : μ.midpoint ≤ 1/32 := by unfold InteriorLaw.midpoint; linarith
  have ht0 : 0 < t := H_pos hm0 (by linarith)
  have htm : t ≤ H (1/32) := H_strictMonoOn.monotoneOn
    ⟨hm0.le,by linarith⟩ ⟨by norm_num,by norm_num⟩ hm1
  have htstar : t ≤ 201/1000 := htm.trans Certificates.SmallMean.entropy_one_over_32_lt.le
  have ht1 : t < 1 := htstar.trans_lt (by norm_num)
  have hS : 0 ≤ S := by
    have h₁ := H_pos μ.a_interior.1 μ.a_interior.2
    have h₂ := H_pos μ.b_interior.1 μ.b_interior.2
    dsimp [S]; linarith
  have hDS : D+S=t := by dsimp [D,S,t,InteriorLaw.entropyDrop]; ring
  have hEst := SmallMean.mean_estimates μ.a_interior.1 hab' μ.b_interior.2 hsmall
  change 0 < D ∧ D ≤ r^2/31 ∧ (4+(1862/2883)*r^2)*D ≤ j ∧ SmallMean.gamma r*D ≤ α at hEst
  obtain ⟨hD,hDr,hj,hα⟩ := hEst
  have hDt : D ≤ t := by linarith
  have hr0 : 0 < r := div_pos (sub_pos.mpr hab')
    (add_pos μ.a_interior.1 μ.b_interior.1)
  have hr1 : r ≤ 1 := by
    apply (div_le_one (add_pos μ.a_interior.1 μ.b_interior.1)).mpr
    linarith [μ.a_interior.1]
  have hslope := SmallMean.slope_small_mean hm0 hm1
  change deriv Scalar.P t ≤ 4+(23/10)*t at hslope
  have hdiff : Scalar.P t-Scalar.P (t-D) ≤ (4+(23/10)*t)*D := by
    have h := Scalar.P_increment_upper (show 0 ≤ t-D by linarith)
      (show t-D ≤ t by linarith) ht0 ht1
    have hmul := mul_le_mul_of_nonneg_left hslope hD.le
    nlinarith only [h,hmul]
  have hend : 0 ≤ Scalar.gap j α D S := by
    have h := SmallMean.endpoint_nonneg_of_estimates hr0 hr1 ht0.le htstar
      hD.le hDt hDr hj hα hdiff
    have htD : t-D=S := by linarith
    rw [htD] at h
    simpa only [Scalar.gap,hDS] using h
  have hzero : Scalar.P D ≤ j :=
    deterministic_cap_bound μ.a_interior.1 μ.a_interior.2 μ.b_interior.1 μ.b_interior.2
  have hs : 0 ≤ s := μ.meanDeficit_mem.1
  have hsS : s ≤ S := by
    have he := μ.e_pos
    have hf := μ.f_pos
    dsimp [s,S,InteriorLaw.meanDeficit]; linarith
  have hgap := Scalar.gap_endpoint_criterion hD.le hS (by rw [hDS]; exact ht1)
    hzero hend hs hsS
  have hcost : j+α*s ≤ μ.cost := by
    have h := LogSum.cost_lower_bound μ
    unfold LogSum.V at h
    rw [max_eq_right hab, min_eq_left hab] at h
    convert! h using 1
    dsimp [j,α,s,InteriorLaw.meanDeficit]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  exact hgap.trans hcost

/-- The small-mean psi branch for arbitrary finite interior laws and entropy splits. -/
theorem small_mean_psi {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsmall : μ.a+μ.b ≤ 1/16) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost :=
  μ.psi_gap_le_splitBound.trans (small_mean_splitBound μ hab hsmall)

/-- The new small-mean region is complete when psi is active at the parent.
The phi-active branch is still part of the unproved upstream Bellman theorem. -/
theorem small_mean_hybrid_of_active_psi {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsmall : μ.a+μ.b ≤ 1/16)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (small_mean_splitBound μ hab hsmall)

end GeneralCK


