-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:17:15.466303+00:00
-- url     : https://prove2.me/theorems/a98844ee-8a28-4e44-9dc5-d3498a3e6efd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0189 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1516 : CellCertificate where
  tauBall := tau1516
  contactCenter := center1516
  contactBall := contact1516
  work := work1516
  center_sq := center_sq1516
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1516.1
  jac_ok := checks1516.2.1
  accepted := checks1516.2.2

def tau1517 : RatBall :=
  ⟨⟨-1/64, -119/320⟩, 3/640⟩
def center1517 : GaussianRat :=
  ⟨-1264209/100000000, -27119647/100000000⟩
def contact1517 : RatBall := localContactBall tau1517 center1517
def work1517 : RoundedTauEval :=
  evalTau precision tau1517 contact1517 logTwoBall

theorem center_sq1517 : (center1517.re : ℝ)^2 +
    (center1517.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1517]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1517 : work1517.theta.ok = true ∧
    work1517.jac.invOK = true ∧ acceptsUnitSq work1517.out = true := by decide +kernel

def cell1517 : CellCertificate where
  tauBall := tau1517
  contactCenter := center1517
  contactBall := contact1517
  work := work1517
  center_sq := center_sq1517
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1517.1
  jac_ok := checks1517.2.1
  accepted := checks1517.2.2

def tau1518 : RatBall :=
  ⟨⟨-7/320, -117/320⟩, 3/640⟩
def center1518 : GaussianRat :=
  ⟨-3519651/200000000, -8314767/31250000⟩
def contact1518 : RatBall := localContactBall tau1518 center1518
def work1518 : RoundedTauEval :=
  evalTau precision tau1518 contact1518 logTwoBall

theorem center_sq1518 : (center1518.re : ℝ)^2 +
    (center1518.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1518]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1518 : work1518.theta.ok = true ∧
    work1518.jac.invOK = true ∧ acceptsUnitSq work1518.out = true := by decide +kernel

def cell1518 : CellCertificate where
  tauBall := tau1518
  contactCenter := center1518
  contactBall := contact1518
  work := work1518
  center_sq := center_sq1518
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1518.1
  jac_ok := checks1518.2.1
  accepted := checks1518.2.2

def tau1519 : RatBall :=
  ⟨⟨-1/64, -117/320⟩, 3/640⟩
def center1519 : GaussianRat :=
  ⟨-1257211/100000000, -66538831/250000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189


