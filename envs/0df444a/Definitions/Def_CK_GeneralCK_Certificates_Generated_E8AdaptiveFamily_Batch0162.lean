-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0162
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0162
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:34:26.826242+00:00
-- url     : https://prove2.me/theorems/401d2c05-078d-49c5-9907-2102c25eb8e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0162.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0162_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1301 : RoundedTauEval :=
  evalTau precision tau1301 contact1301 logTwoBall

theorem center_sq1301 : (center1301.re : ℝ)^2 +
    (center1301.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1301]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1301 : work1301.theta.ok = true ∧
    work1301.jac.invOK = true ∧ acceptsUnitSq work1301.out = true := by decide +kernel

def cell1301 : CellCertificate where
  tauBall := tau1301
  contactCenter := center1301
  contactBall := contact1301
  work := work1301
  center_sq := center_sq1301
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1301.1
  jac_ok := checks1301.2.1
  accepted := checks1301.2.2

def tau1302 : RatBall :=
  ⟨⟨-19/64, -81/320⟩, 3/640⟩
def center1302 : GaussianRat :=
  ⟨-211952789/1000000000, -162910673/1000000000⟩
def contact1302 : RatBall := localContactBall tau1302 center1302
def work1302 : RoundedTauEval :=
  evalTau precision tau1302 contact1302 logTwoBall

theorem center_sq1302 : (center1302.re : ℝ)^2 +
    (center1302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1302 : work1302.theta.ok = true ∧
    work1302.jac.invOK = true ∧ acceptsUnitSq work1302.out = true := by decide +kernel

def cell1302 : CellCertificate where
  tauBall := tau1302
  contactCenter := center1302
  contactBall := contact1302
  work := work1302
  center_sq := center_sq1302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1302.1
  jac_ok := checks1302.2.1
  accepted := checks1302.2.2

def tau1303 : RatBall :=
  ⟨⟨-93/320, -81/320⟩, 3/640⟩
def center1303 : GaussianRat :=
  ⟨-103905761/500000000, -163537217/1000000000⟩
def contact1303 : RatBall := localContactBall tau1303 center1303
def work1303 : RoundedTauEval :=
  evalTau precision tau1303 contact1303 logTwoBall

theorem center_sq1303 : (center1303.re : ℝ)^2 +
    (center1303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1303 : work1303.theta.ok = true ∧
    work1303.jac.invOK = true ∧ acceptsUnitSq work1303.out = true := by decide +kernel

def cell1303 : CellCertificate where
  tauBall := tau1303
  contactCenter := center1303
  contactBall := contact1303
  work := work1303
  center_sq := center_sq1303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1303.1
  jac_ok := checks1303.2.1
  accepted := checks1303.2.2

def cells : List CellCertificate := [cell1296, cell1297, cell1298, cell1299, cell1300, cell1301, cell1302, cell1303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162


