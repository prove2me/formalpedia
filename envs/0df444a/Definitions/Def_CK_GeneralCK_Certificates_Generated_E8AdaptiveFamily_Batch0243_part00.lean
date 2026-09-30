-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:04:48.199113+00:00
-- url     : https://prove2.me/theorems/6ca1e813-b80a-4276-9c99-82b489fbb5de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0243 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1944 : RatBall :=
  ⟨⟨-17/64, 89/320⟩, 3/640⟩
def center1944 : GaussianRat :=
  ⟨-24194269/125000000, 5716477/31250000⟩
def contact1944 : RatBall := localContactBall tau1944 center1944
def work1944 : RoundedTauEval :=
  evalTau precision tau1944 contact1944 logTwoBall

theorem center_sq1944 : (center1944.re : ℝ)^2 +
    (center1944.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1944]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1944 : work1944.theta.ok = true ∧
    work1944.jac.invOK = true ∧ acceptsUnitSq work1944.out = true := by decide +kernel

def cell1944 : CellCertificate where
  tauBall := tau1944
  contactCenter := center1944
  contactBall := contact1944
  work := work1944
  center_sq := center_sq1944
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1944.1
  jac_ok := checks1944.2.1
  accepted := checks1944.2.2

def tau1945 : RatBall :=
  ⟨⟨-87/320, 91/320⟩, 3/640⟩
def center1945 : GaussianRat :=
  ⟨-49621711/250000000, 186511513/1000000000⟩
def contact1945 : RatBall := localContactBall tau1945 center1945
def work1945 : RoundedTauEval :=
  evalTau precision tau1945 contact1945 logTwoBall

theorem center_sq1945 : (center1945.re : ℝ)^2 +
    (center1945.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1945]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1945 : work1945.theta.ok = true ∧
    work1945.jac.invOK = true ∧ acceptsUnitSq work1945.out = true := by decide +kernel

def cell1945 : CellCertificate where
  tauBall := tau1945
  contactCenter := center1945
  contactBall := contact1945
  work := work1945
  center_sq := center_sq1945
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1945.1
  jac_ok := checks1945.2.1
  accepted := checks1945.2.2

def tau1946 : RatBall :=
  ⟨⟨-17/64, 91/320⟩, 3/640⟩
def center1946 : GaussianRat :=
  ⟨-97111567/500000000, 37439051/200000000⟩
def contact1946 : RatBall := localContactBall tau1946 center1946

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243


