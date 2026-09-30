-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0208
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0208
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:57:07.339383+00:00
-- url     : https://prove2.me/theorems/6ebe3aaf-8b8c-4d15-ba13-c108bc3cd974
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0208.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0208_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1670 : RoundedTauEval :=
  evalTau precision tau1670 contact1670 logTwoBall

theorem center_sq1670 : (center1670.re : ℝ)^2 +
    (center1670.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1670]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1670 : work1670.theta.ok = true ∧
    work1670.jac.invOK = true ∧ acceptsUnitSq work1670.out = true := by decide +kernel

def cell1670 : CellCertificate where
  tauBall := tau1670
  contactCenter := center1670
  contactBall := contact1670
  work := work1670
  center_sq := center_sq1670
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1670.1
  jac_ok := checks1670.2.1
  accepted := checks1670.2.2

def tau1671 : RatBall :=
  ⟨⟨41/320, -107/320⟩, 3/640⟩
def center1671 : GaussianRat :=
  ⟨99508871/1000000000, -236497219/1000000000⟩
def contact1671 : RatBall := localContactBall tau1671 center1671
def work1671 : RoundedTauEval :=
  evalTau precision tau1671 contact1671 logTwoBall

theorem center_sq1671 : (center1671.re : ℝ)^2 +
    (center1671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1671 : work1671.theta.ok = true ∧
    work1671.jac.invOK = true ∧ acceptsUnitSq work1671.out = true := by decide +kernel

def cell1671 : CellCertificate where
  tauBall := tau1671
  contactCenter := center1671
  contactBall := contact1671
  work := work1671
  center_sq := center_sq1671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1671.1
  jac_ok := checks1671.2.1
  accepted := checks1671.2.2

def cells : List CellCertificate := [cell1664, cell1665, cell1666, cell1667, cell1668, cell1669, cell1670, cell1671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208


