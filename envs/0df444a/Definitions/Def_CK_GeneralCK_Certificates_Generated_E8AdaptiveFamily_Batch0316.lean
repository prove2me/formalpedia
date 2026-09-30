-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0316
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0316
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:57:34.807801+00:00
-- url     : https://prove2.me/theorems/85e90fcb-1460-409e-855f-455d9003153b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0316.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0316_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2534 : (center2534.re : ℝ)^2 +
    (center2534.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2534]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2534 : work2534.theta.ok = true ∧
    work2534.jac.invOK = true ∧ acceptsUnitSq work2534.out = true := by decide +kernel

def cell2534 : CellCertificate where
  tauBall := tau2534
  contactCenter := center2534
  contactBall := contact2534
  work := work2534
  center_sq := center_sq2534
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2534.1
  jac_ok := checks2534.2.1
  accepted := checks2534.2.2

def tau2535 : RatBall :=
  ⟨⟨71/320, 103/320⟩, 3/640⟩
def center2535 : GaussianRat :=
  ⟨83877437/500000000, 218307477/1000000000⟩
def contact2535 : RatBall := localContactBall tau2535 center2535
def work2535 : RoundedTauEval :=
  evalTau precision tau2535 contact2535 logTwoBall

theorem center_sq2535 : (center2535.re : ℝ)^2 +
    (center2535.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2535]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2535 : work2535.theta.ok = true ∧
    work2535.jac.invOK = true ∧ acceptsUnitSq work2535.out = true := by decide +kernel

def cell2535 : CellCertificate where
  tauBall := tau2535
  contactCenter := center2535
  contactBall := contact2535
  work := work2535
  center_sq := center_sq2535
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2535.1
  jac_ok := checks2535.2.1
  accepted := checks2535.2.2

def cells : List CellCertificate := [cell2528, cell2529, cell2530, cell2531, cell2532, cell2533, cell2534, cell2535]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316


