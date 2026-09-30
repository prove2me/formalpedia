-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:03:28.481979+00:00
-- url     : https://prove2.me/theorems/b897ac11-88e5-4b4c-9f8d-49bf0c51ae2d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0248.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1990 : RoundedTauEval :=
  evalTau precision tau1990 contact1990 logTwoBall

theorem center_sq1990 : (center1990.re : ℝ)^2 +
    (center1990.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1990]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1990 : work1990.theta.ok = true ∧
    work1990.jac.invOK = true ∧ acceptsUnitSq work1990.out = true := by decide +kernel

def cell1990 : CellCertificate where
  tauBall := tau1990
  contactCenter := center1990
  contactBall := contact1990
  work := work1990
  center_sq := center_sq1990
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1990.1
  jac_ok := checks1990.2.1
  accepted := checks1990.2.2

def tau1991 : RatBall :=
  ⟨⟨-77/320, 99/320⟩, 3/640⟩
def center1991 : GaussianRat :=
  ⟨-179660917/1000000000, 207308367/1000000000⟩
def contact1991 : RatBall := localContactBall tau1991 center1991
def work1991 : RoundedTauEval :=
  evalTau precision tau1991 contact1991 logTwoBall

theorem center_sq1991 : (center1991.re : ℝ)^2 +
    (center1991.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1991]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1991 : work1991.theta.ok = true ∧
    work1991.jac.invOK = true ∧ acceptsUnitSq work1991.out = true := by decide +kernel

def cell1991 : CellCertificate where
  tauBall := tau1991
  contactCenter := center1991
  contactBall := contact1991
  work := work1991
  center_sq := center_sq1991
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1991.1
  jac_ok := checks1991.2.1
  accepted := checks1991.2.2

def cells : List CellCertificate := [cell1984, cell1985, cell1986, cell1987, cell1988, cell1989, cell1990, cell1991]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248


