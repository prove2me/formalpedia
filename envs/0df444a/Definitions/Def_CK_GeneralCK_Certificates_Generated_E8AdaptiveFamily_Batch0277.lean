-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0277
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0277
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:41:09.008464+00:00
-- url     : https://prove2.me/theorems/5dded177-b7e7-462f-9e6c-77ac8793be21
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0277.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0277_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2222 : (center2222.re : ℝ)^2 +
    (center2222.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2222]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2222 : work2222.theta.ok = true ∧
    work2222.jac.invOK = true ∧ acceptsUnitSq work2222.out = true := by decide +kernel

def cell2222 : CellCertificate where
  tauBall := tau2222
  contactCenter := center2222
  contactBall := contact2222
  work := work2222
  center_sq := center_sq2222
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2222.1
  jac_ok := checks2222.2.1
  accepted := checks2222.2.2

def tau2223 : RatBall :=
  ⟨⟨113/320, 61/320⟩, 3/640⟩
def center2223 : GaussianRat :=
  ⟨242396513/1000000000, 117649273/1000000000⟩
def contact2223 : RatBall := localContactBall tau2223 center2223
def work2223 : RoundedTauEval :=
  evalTau precision tau2223 contact2223 logTwoBall

theorem center_sq2223 : (center2223.re : ℝ)^2 +
    (center2223.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2223]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2223 : work2223.theta.ok = true ∧
    work2223.jac.invOK = true ∧ acceptsUnitSq work2223.out = true := by decide +kernel

def cell2223 : CellCertificate where
  tauBall := tau2223
  contactCenter := center2223
  contactBall := contact2223
  work := work2223
  center_sq := center_sq2223
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2223.1
  jac_ok := checks2223.2.1
  accepted := checks2223.2.2

def cells : List CellCertificate := [cell2216, cell2217, cell2218, cell2219, cell2220, cell2221, cell2222, cell2223]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277


