-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:09:52.959892+00:00
-- url     : https://prove2.me/theorems/94e3affd-765a-431c-9ac7-03d35fb7f890
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0164 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0164_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1316 : CellCertificate where
  tauBall := tau1316
  contactCenter := center1316
  contactBall := contact1316
  work := work1316
  center_sq := center_sq1316
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1316.1
  jac_ok := checks1316.2.1
  accepted := checks1316.2.2

def tau1317 : RatBall :=
  ⟨⟨-77/320, -19/64⟩, 3/640⟩
def center1317 : GaussianRat :=
  ⟨-35656681/200000000, -198539511/1000000000⟩
def contact1317 : RatBall := localContactBall tau1317 center1317
def work1317 : RoundedTauEval :=
  evalTau precision tau1317 contact1317 logTwoBall

theorem center_sq1317 : (center1317.re : ℝ)^2 +
    (center1317.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1317]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1317 : work1317.theta.ok = true ∧
    work1317.jac.invOK = true ∧ acceptsUnitSq work1317.out = true := by decide +kernel

def cell1317 : CellCertificate where
  tauBall := tau1317
  contactCenter := center1317
  contactBall := contact1317
  work := work1317
  center_sq := center_sq1317
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1317.1
  jac_ok := checks1317.2.1
  accepted := checks1317.2.2

def tau1318 : RatBall :=
  ⟨⟨-79/320, -93/320⟩, 3/640⟩
def center1318 : GaussianRat :=
  ⟨-90986481/500000000, -24189551/125000000⟩
def contact1318 : RatBall := localContactBall tau1318 center1318
def work1318 : RoundedTauEval :=
  evalTau precision tau1318 contact1318 logTwoBall

theorem center_sq1318 : (center1318.re : ℝ)^2 +
    (center1318.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1318]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1318 : work1318.theta.ok = true ∧
    work1318.jac.invOK = true ∧ acceptsUnitSq work1318.out = true := by decide +kernel

def cell1318 : CellCertificate where
  tauBall := tau1318
  contactCenter := center1318
  contactBall := contact1318
  work := work1318
  center_sq := center_sq1318
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1318.1
  jac_ok := checks1318.2.1
  accepted := checks1318.2.2

def tau1319 : RatBall :=
  ⟨⟨-77/320, -93/320⟩, 3/640⟩
def center1319 : GaussianRat :=
  ⟨-44405679/250000000, -194173939/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164


