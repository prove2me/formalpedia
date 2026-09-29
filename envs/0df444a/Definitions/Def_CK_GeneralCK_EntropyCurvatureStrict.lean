-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyCurvatureStrict
-- name    : CK_GeneralCK_EntropyCurvatureStrict
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:48:25.525418+00:00
-- url     : https://prove2.me/theorems/157ea0ef-87d8-4f23-9f55-555ac4359720
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyCurvatureStrict` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyCurvatureStrict` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyCurvatureStrict` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyCurvatureStrict (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyCurvatureStrict.lean)

import Definitions.Def_CK_GeneralCK_PhysicalSlope
import Definitions.Def_CK_GeneralCK_EntropyRadialDerivatives
import Definitions.Def_CK_GeneralCK_Certificates_PilotData

namespace GeneralCK.Scalar

theorem curvatureNumerator_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < curvatureNumerator v := by
  have hl := logit_ge_twice_imbalance hv hv'.le
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ v^2+(1-v)^2 by positivity)
  have hp : 0 < (1-2*v)^3 := pow_pos (by linarith) 3
  have hbound : (1-2*v)^3 ≤ curvatureNumerator v := by
    unfold curvatureNumerator
    nlinarith
  exact hp.trans_le hbound

theorem etaCurvature_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    0 < etaCurvature h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hvc : 0 < 1-entropyInverse h := by linarith
  have hJ := J_pos hv hv'
  unfold etaCurvature
  exact div_pos (curvatureNumerator_pos hv hv') (by positivity)

theorem deriv2_eta_pos {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    0 < deriv (deriv eta) h := by
  rw [(hasDerivAt_deriv_eta h0 h1).deriv]
  exact etaCurvature_pos h0 h1

end GeneralCK.Scalar

namespace GeneralCK
open Certificates.Mixed

theorem kap_ge_log_two {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    Real.log 2 ≤ kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  have hu : v*(1-v) ≤ 1/4 := by nlinarith [sq_nonneg (v-1/2)]
  have hh : Real.log (v*(1-v)) ≤ -2*Real.log 2 := by
    calc
      Real.log (v*(1-v)) ≤ Real.log (1/4) := Real.log_le_log hp hu
      _ = -2*Real.log 2 := by
        rw [show (1/4:ℝ) = (2^2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
        norm_num
  unfold kap
  linarith

theorem kap_sq_gap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < 2*kap v-(1-2*v)^2 := by
  have hk := kap_ge_log_two hv (by linarith)
  have hL := Certificates.PilotData.log_two.1
  norm_num only [div_one] at hL
  have hr : (1-2*v)^2 ≤ 1 := by nlinarith
  linarith

theorem mixed_profile_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    0 < profile v := by
  have hvc : 0 < 1-v := by linarith
  have hr : 0 < 1-2*v := by linarith
  have hn0 : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hk := kap_pos hv hv'
  have hg := kap_sq_gap_pos hv hv'
  unfold profile
  positivity

theorem deriv2_F_radius_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < deriv (deriv (fun r => F r h)) z := by
  have hp : 0 < z*deriv (deriv (fun r => F r h)) z := by
    rw [radius_mul_deriv2_F_eq_profile hz hh]
    exact mixed_profile_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  exact (mul_pos_iff_of_pos_left hz).mp hp

theorem deriv_radialPhi_radius_entropy_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < deriv (fun q => deriv (fun r => radialPhi r q) z) h := by
  rw [deriv_radialPhi_radius_entropy hz hh]
  exact mul_pos (div_pos hz hh) (deriv2_F_radius_pos hz hh)

theorem deriv2_F_entropy_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < deriv (deriv (F z)) h := by
  rw [deriv2_F_entropy hz hh]
  exact mul_pos (sq_pos_of_pos (div_pos hz hh)) (deriv2_F_radius_pos hz hh)

end GeneralCK


