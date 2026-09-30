-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0247
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0247
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:38:35.664969+00:00
-- url     : https://prove2.me/theorems/60303328-58ca-4231-ba00-80fcd51b7ab1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0247.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0247_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1981 : work1981.theta.ok = true ∧
    work1981.jac.invOK = true ∧ acceptsUnitSq work1981.out = true := by decide +kernel

def cell1981 : CellCertificate where
  tauBall := tau1981
  contactCenter := center1981
  contactBall := contact1981
  work := work1981
  center_sq := center_sq1981
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1981.1
  jac_ok := checks1981.2.1
  accepted := checks1981.2.2

def tau1982 : RatBall :=
  ⟨⟨-13/64, 19/64⟩, 3/640⟩
def center1982 : GaussianRat :=
  ⟨-30345869/200000000, 40464617/200000000⟩
def contact1982 : RatBall := localContactBall tau1982 center1982
def work1982 : RoundedTauEval :=
  evalTau precision tau1982 contact1982 logTwoBall

theorem center_sq1982 : (center1982.re : ℝ)^2 +
    (center1982.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1982]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1982 : work1982.theta.ok = true ∧
    work1982.jac.invOK = true ∧ acceptsUnitSq work1982.out = true := by decide +kernel

def cell1982 : CellCertificate where
  tauBall := tau1982
  contactCenter := center1982
  contactBall := contact1982
  work := work1982
  center_sq := center_sq1982
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1982.1
  jac_ok := checks1982.2.1
  accepted := checks1982.2.2

def tau1983 : RatBall :=
  ⟨⟨-17/64, 97/320⟩, 3/640⟩
def center1983 : GaussianRat :=
  ⟨-49086427/250000000, 200064207/1000000000⟩
def contact1983 : RatBall := localContactBall tau1983 center1983
def work1983 : RoundedTauEval :=
  evalTau precision tau1983 contact1983 logTwoBall

theorem center_sq1983 : (center1983.re : ℝ)^2 +
    (center1983.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1983]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1983 : work1983.theta.ok = true ∧
    work1983.jac.invOK = true ∧ acceptsUnitSq work1983.out = true := by decide +kernel

def cell1983 : CellCertificate where
  tauBall := tau1983
  contactCenter := center1983
  contactBall := contact1983
  work := work1983
  center_sq := center_sq1983
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1983.1
  jac_ok := checks1983.2.1
  accepted := checks1983.2.2

def cells : List CellCertificate := [cell1976, cell1977, cell1978, cell1979, cell1980, cell1981, cell1982, cell1983]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247


