-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0240_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:33.006176+00:00
-- url     : https://prove2.me/theorems/0aefe940-ebc4-461d-9af9-cc6f0a6abd7a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0240 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1920 : RatBall :=
  ⟨⟨-89/320, 83/320⟩, 3/640⟩
def center1920 : GaussianRat :=
  ⟨-100043853/500000000, 84478333/500000000⟩
def contact1920 : RatBall := localContactBall tau1920 center1920
def work1920 : RoundedTauEval :=
  evalTau precision tau1920 contact1920 logTwoBall

theorem center_sq1920 : (center1920.re : ℝ)^2 +
    (center1920.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1920]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1920 : work1920.theta.ok = true ∧
    work1920.jac.invOK = true ∧ acceptsUnitSq work1920.out = true := by decide +kernel

def cell1920 : CellCertificate where
  tauBall := tau1920
  contactCenter := center1920
  contactBall := contact1920
  work := work1920
  center_sq := center_sq1920
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1920.1
  jac_ok := checks1920.2.1
  accepted := checks1920.2.2

def tau1921 : RatBall :=
  ⟨⟨-19/64, 17/64⟩, 3/640⟩
def center1921 : GaussianRat :=
  ⟨-42650399/200000000, 171191029/1000000000⟩
def contact1921 : RatBall := localContactBall tau1921 center1921
def work1921 : RoundedTauEval :=
  evalTau precision tau1921 contact1921 logTwoBall

theorem center_sq1921 : (center1921.re : ℝ)^2 +
    (center1921.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1921]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1921 : work1921.theta.ok = true ∧
    work1921.jac.invOK = true ∧ acceptsUnitSq work1921.out = true := by decide +kernel

def cell1921 : CellCertificate where
  tauBall := tau1921
  contactCenter := center1921
  contactBall := contact1921
  work := work1921
  center_sq := center_sq1921
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1921.1
  jac_ok := checks1921.2.1
  accepted := checks1921.2.2

def tau1922 : RatBall :=
  ⟨⟨-93/320, 17/64⟩, 3/640⟩
def center1922 : GaussianRat :=
  ⟨-104546899/500000000, 171855447/1000000000⟩
def contact1922 : RatBall := localContactBall tau1922 center1922
def work1922 : RoundedTauEval :=
  evalTau precision tau1922 contact1922 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240


