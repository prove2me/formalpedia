-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0313
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0313
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:46:46.053876+00:00
-- url     : https://prove2.me/theorems/bdf7caa0-5090-4d6f-8838-23fe301a5b7e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0313.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0313_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2509 : work2509.theta.ok = true ∧
    work2509.jac.invOK = true ∧ acceptsUnitSq work2509.out = true := by decide +kernel

def cell2509 : CellCertificate where
  tauBall := tau2509
  contactCenter := center2509
  contactBall := contact2509
  work := work2509
  center_sq := center_sq2509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2509.1
  jac_ok := checks2509.2.1
  accepted := checks2509.2.2

def tau2510 : RatBall :=
  ⟨⟨101/320, 77/320⟩, 3/640⟩
def center2510 : GaussianRat :=
  ⟨111496867/500000000, 152848327/1000000000⟩
def contact2510 : RatBall := localContactBall tau2510 center2510
def work2510 : RoundedTauEval :=
  evalTau precision tau2510 contact2510 logTwoBall

theorem center_sq2510 : (center2510.re : ℝ)^2 +
    (center2510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2510 : work2510.theta.ok = true ∧
    work2510.jac.invOK = true ∧ acceptsUnitSq work2510.out = true := by decide +kernel

def cell2510 : CellCertificate where
  tauBall := tau2510
  contactCenter := center2510
  contactBall := contact2510
  work := work2510
  center_sq := center_sq2510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2510.1
  jac_ok := checks2510.2.1
  accepted := checks2510.2.2

def tau2511 : RatBall :=
  ⟨⟨103/320, 77/320⟩, 3/640⟩
def center2511 : GaussianRat :=
  ⟨113522317/500000000, 152229153/1000000000⟩
def contact2511 : RatBall := localContactBall tau2511 center2511
def work2511 : RoundedTauEval :=
  evalTau precision tau2511 contact2511 logTwoBall

theorem center_sq2511 : (center2511.re : ℝ)^2 +
    (center2511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2511 : work2511.theta.ok = true ∧
    work2511.jac.invOK = true ∧ acceptsUnitSq work2511.out = true := by decide +kernel

def cell2511 : CellCertificate where
  tauBall := tau2511
  contactCenter := center2511
  contactBall := contact2511
  work := work2511
  center_sq := center_sq2511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2511.1
  jac_ok := checks2511.2.1
  accepted := checks2511.2.2

def cells : List CellCertificate := [cell2504, cell2505, cell2506, cell2507, cell2508, cell2509, cell2510, cell2511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313


