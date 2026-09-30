-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0272
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0272
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:56:52.160534+00:00
-- url     : https://prove2.me/theorems/5039d3df-9e50-4f52-83a2-155e9a0b9c04
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0272.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0272_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2182 : RatBall := localContactBall tau2182 center2182
def work2182 : RoundedTauEval :=
  evalTau precision tau2182 contact2182 logTwoBall

theorem center_sq2182 : (center2182.re : ℝ)^2 +
    (center2182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2182 : work2182.theta.ok = true ∧
    work2182.jac.invOK = true ∧ acceptsUnitSq work2182.out = true := by decide +kernel

def cell2182 : CellCertificate where
  tauBall := tau2182
  contactCenter := center2182
  contactBall := contact2182
  work := work2182
  center_sq := center_sq2182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2182.1
  jac_ok := checks2182.2.1
  accepted := checks2182.2.2

def tau2183 : RatBall :=
  ⟨⟨-13/320, 113/320⟩, 3/640⟩
def center2183 : GaussianRat :=
  ⟨-32309979/1000000000, 127843073/500000000⟩
def contact2183 : RatBall := localContactBall tau2183 center2183
def work2183 : RoundedTauEval :=
  evalTau precision tau2183 contact2183 logTwoBall

theorem center_sq2183 : (center2183.re : ℝ)^2 +
    (center2183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2183]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2183 : work2183.theta.ok = true ∧
    work2183.jac.invOK = true ∧ acceptsUnitSq work2183.out = true := by decide +kernel

def cell2183 : CellCertificate where
  tauBall := tau2183
  contactCenter := center2183
  contactBall := contact2183
  work := work2183
  center_sq := center_sq2183
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2183.1
  jac_ok := checks2183.2.1
  accepted := checks2183.2.2

def cells : List CellCertificate := [cell2176, cell2177, cell2178, cell2179, cell2180, cell2181, cell2182, cell2183]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272


