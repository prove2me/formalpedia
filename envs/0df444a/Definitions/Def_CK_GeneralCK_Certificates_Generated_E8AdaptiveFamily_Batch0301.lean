-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0301
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0301
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:20:19.314756+00:00
-- url     : https://prove2.me/theorems/5e9348dc-372e-4f5f-99fa-e15a652efef9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0301.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0301_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2414 : RoundedTauEval :=
  evalTau precision tau2414 contact2414 logTwoBall

theorem center_sq2414 : (center2414.re : ℝ)^2 +
    (center2414.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2414]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2414 : work2414.theta.ok = true ∧
    work2414.jac.invOK = true ∧ acceptsUnitSq work2414.out = true := by decide +kernel

def cell2414 : CellCertificate where
  tauBall := tau2414
  contactCenter := center2414
  contactBall := contact2414
  work := work2414
  center_sq := center_sq2414
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2414.1
  jac_ok := checks2414.2.1
  accepted := checks2414.2.2

def tau2415 : RatBall :=
  ⟨⟨47/320, 113/320⟩, 3/640⟩
def center2415 : GaussianRat :=
  ⟨115394221/1000000000, 124626021/500000000⟩
def contact2415 : RatBall := localContactBall tau2415 center2415
def work2415 : RoundedTauEval :=
  evalTau precision tau2415 contact2415 logTwoBall

theorem center_sq2415 : (center2415.re : ℝ)^2 +
    (center2415.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2415 : work2415.theta.ok = true ∧
    work2415.jac.invOK = true ∧ acceptsUnitSq work2415.out = true := by decide +kernel

def cell2415 : CellCertificate where
  tauBall := tau2415
  contactCenter := center2415
  contactBall := contact2415
  work := work2415
  center_sq := center_sq2415
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2415.1
  jac_ok := checks2415.2.1
  accepted := checks2415.2.2

def cells : List CellCertificate := [cell2408, cell2409, cell2410, cell2411, cell2412, cell2413, cell2414, cell2415]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301


