-- Prove2me | Definitions.Def_CK_GeneralCK_LowInformationRegion
-- name    : CK_GeneralCK_LowInformationRegion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:37:38.821189+00:00
-- url     : https://prove2.me/theorems/59837c5d-7f4a-4f39-8f9e-f6f63b6bd1fb
-- title:
--   Courtade–Kumar proof module `GeneralCK.LowInformationRegion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LowInformationRegion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LowInformationRegion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LowInformationRegion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LowInformationRegion.lean)

import Definitions.Def_CK_GeneralCK_LowInformationProfile
import Definitions.Def_CK_GeneralCK_LowInformationMeans
import Definitions.Def_CK_GeneralCK_BellmanSymmetry
import Definitions.Def_CK_GeneralCK_LogSum
import Definitions.Def_CK_GeneralCK_DeterministicCap

namespace GeneralCK

/-- The scalar log-sum comparison in canonical coordinates at low information. -/
theorem low_information_splitBound_canonical {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsum : μ.a+μ.b ≤ 1) (hI : μ.information ≤ 1/100) :
    μ.splitBound ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hab'
  · have hD : μ.entropyDrop = 0 := by
      unfold InteriorLaw.entropyDrop InteriorLaw.midpoint
      rw [← heq, show (μ.a+μ.a)/2 = μ.a by ring]
      ring
    have hc : 0 ≤ μ.cost := by
      simpa [← heq, interiorCost] using LogSum.cost_lower_bound μ
    simpa only [InteriorLaw.splitBound,hD,zero_add,sub_self] using hc
  let r := (μ.b-μ.a)/(μ.a+μ.b)
  let D := μ.entropyDrop
  let s := μ.meanDeficit
  let j := interiorCost μ.a μ.b
  let α := (μ.b-μ.a)^2/(2*μ.b*(1-μ.a))
  have hEst := LowInformation.mean_estimates μ.a_interior.1 hab' μ.b_interior.2 hsum
  change 0 < D ∧ (4+r^2/2)*D ≤ j at hEst
  obtain ⟨hD,hj⟩ := hEst
  have hs : 0 ≤ s := μ.meanDeficit_mem.1
  have hcap : D+s ≤ 1/100 := by rw [μ.information_eq] at hI; exact hI
  have hcost : j+α*s ≤ μ.cost := by
    have h := LogSum.cost_lower_bound μ
    unfold LogSum.V at h
    rw [max_eq_right hab, min_eq_left hab] at h
    convert! h using 1
    dsimp [j,α,s,InteriorLaw.meanDeficit]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  by_cases hr : r ≤ 1/5
  · have hα := LowInformation.low_ratio_alpha μ.a_interior.1 hab' μ.b_interior.2 hsum hr
    change (19/10)*D ≤ α at hα
    have hzero : Scalar.P D ≤ j := deterministic_cap_bound
      μ.a_interior.1 μ.a_interior.2 μ.b_interior.1 μ.b_interior.2
    have h := Scalar.low_information_increment_bilinear hD.le hs hcap
    have hmul := mul_le_mul_of_nonneg_right hα hs
    have hb : μ.splitBound ≤ j+α*s := by
      change Scalar.P (D+s)-Scalar.P s ≤ j+α*s
      linarith
    exact hb.trans hcost
  · have hrge : 1/5 ≤ r := (lt_of_not_ge hr).le
    have hsq := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/5) hrge
    have hcoef : 0 ≤ 4+r^2/2-4019/1000 := by nlinarith only [hsq]
    have hmul := mul_nonneg hcoef hD.le
    have h := Scalar.low_information_increment_linear hD.le hs hcap
    have hα : 0 ≤ α := by
      have hb := μ.b_interior.1
      have ha : 0 < 1-μ.a := sub_pos.mpr μ.a_interior.2
      dsimp [α]; positivity
    have hαs := mul_nonneg hα hs
    change Scalar.P (D+s)-Scalar.P s ≤ μ.cost
    nlinarith only [h,hmul,hj,hcost,hαs]

/-- The entire low-information psi comparison, for arbitrary mean orientation. -/
theorem low_information_splitBound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hI : μ.information ≤ 1/100) : μ.splitBound ≤ μ.cost := by
  obtain ⟨ν,hab,hsum,hb,hi,hc⟩ := μ.exists_canonical_split
  have h := low_information_splitBound_canonical ν hab hsum (by rw [hi]; exact hI)
  rwa [hb,hc] at h

theorem low_information_psi {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hI : μ.information ≤ 1/100) : candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost :=
  μ.psi_gap_le_splitBound.trans (low_information_splitBound μ hI)

/-- As with every psi comparison, promotion to the hybrid uses activity at the parent. -/
theorem low_information_hybrid_of_active_psi {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hI : μ.information ≤ 1/100)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := μ.gap_le_of_splitBound hactive (low_information_splitBound μ hI)

end GeneralCK


