-- Prove2me | Definitions.Def_CK_GeneralCK_PhiEntropyConvexity
-- name    : CK_GeneralCK_PhiEntropyConvexity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:32:51.056979+00:00
-- url     : https://prove2.me/theorems/8d57688a-de79-4d54-a588-70bed4c7bcb8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PhiEntropyConvexity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PhiEntropyConvexity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PhiEntropyConvexity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PhiEntropyConvexity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PhiEntropyConvexity.lean)

import Definitions.Def_CK_GeneralCK_EntropyCurvatureLargeTail
import Definitions.Def_CK_GeneralCK_EntropyCurvatureSmallTail
import Definitions.Def_CK_GeneralCK_EntropyCurvatureReduction
import Definitions.Def_CK_GeneralCK_EntropyCurvatureStrict
import Definitions.Def_CK_GeneralCK_Certificates_EntropyCurvatureCertificate

namespace GeneralCK
open Set

namespace EntropyCurvature

/-- The entire contact interval: two analytic tails and the checked compact cover. -/
theorem scalar_signs {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) : 0 < P v ∧ 0 < R v := by
  by_cases hl : v ≤ 1/100
  · exact large_tail hv hl
  · by_cases hu : 11/24 ≤ v
    · exact small_tail hv hu hv'
    · exact Certificates.EntropyCurvature.entropy_curvature_compact v
        (lt_of_not_ge hl).le (lt_of_not_ge hu).le

theorem beta_antitoneOn : AntitoneOn beta (Ioo 0 (1/2)) :=
  beta_antitoneOn_of_R (fun _ hv => (scalar_signs hv.1 hv.2).2.le)

end EntropyCurvature

/-- Strict entropy curvature at positive radius, including its positive cap endpoint. -/
theorem deriv2_radialPhi_entropy_pos {z h : ℝ} (hz : 0 < z) (hz' : z < 1)
    (hh : 0 < h) (hcap : h ≤ H ((1-z)/2)) :
    0 < deriv (deriv (radialPhi z)) h :=
  EntropyCurvature.deriv2_radialPhi_entropy_pos_of_signs
    (fun _ hv => (EntropyCurvature.scalar_signs hv.1 hv.2).1)
    (fun _ hv => (EntropyCurvature.scalar_signs hv.1 hv.2).2.le) hz hz' hh hcap

/-- Feasible entropy convexity with both scalar sign premises discharged. -/
theorem radialPhi_entropy_convexOn {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    ConvexOn ℝ (Ioc 0 (H ((1-z)/2))) (radialPhi z) :=
  EntropyCurvature.radialPhi_entropy_convexOn_of_signs
    (fun _ hv => (EntropyCurvature.scalar_signs hv.1 hv.2).1)
    (fun _ hv => (EntropyCurvature.scalar_signs hv.1 hv.2).2.le) hz hz'

/-- Strict curvature on the feasible entropy interior, also at zero radius. -/
theorem deriv2_radialPhi_entropy_pos_feasible {z h : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) (hh : 0 < h) (hcap : h < H ((1-z)/2)) :
    0 < deriv (deriv (radialPhi z)) h := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [EntropyCurvature.radialPhi_zero]
    exact Scalar.deriv2_eta_pos hh (hcap.trans_le (H_le_one _))
  · exact deriv2_radialPhi_entropy_pos hz hz' hh hcap.le

theorem entropy_abs_imbalance (m : ℝ) : H ((1-|1-2*m|)/2) = H m := by
  by_cases hm : m ≤ 1/2
  · rw [abs_of_nonneg (by linarith),show (1-(1-2*m))/2=m by ring]
  · rw [abs_of_neg (by linarith),show (1-(-(1-2*m)))/2=1-m by ring,H_complement]

/-- The original mean/entropy candidate is convex throughout its positive feasible fiber. -/
theorem phi_entropy_convexOn {m : ℝ} (hm : 0 < m) (hm' : m < 1) :
    ConvexOn ℝ (Ioc 0 (H m)) (phi m) := by
  have hz : |1-2*m| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  have h := radialPhi_entropy_convexOn (abs_nonneg (1-2*m)) hz
  rw [entropy_abs_imbalance] at h
  exact h

theorem deriv2_phi_entropy_pos {m h : ℝ} (hm : 0 < m) (hm' : m < 1)
    (hh : 0 < h) (hcap : h < H m) : 0 < deriv (deriv (phi m)) h := by
  apply deriv2_radialPhi_entropy_pos_feasible (abs_nonneg (1-2*m))
    (abs_lt.mpr ⟨by linarith,by linarith⟩) hh
  rwa [entropy_abs_imbalance]

end GeneralCK


