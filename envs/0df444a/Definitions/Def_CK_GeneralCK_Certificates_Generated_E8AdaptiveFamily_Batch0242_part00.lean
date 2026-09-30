-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:04:55.942981+00:00
-- url     : https://prove2.me/theorems/a46989a2-2574-49ef-8ba1-9c49d5955d82
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0242 (part 1 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1936 : RatBall :=
  ⟨⟨-81/320, 87/320⟩, 3/640⟩
def center1936 : GaussianRat :=
  ⟨-9218121/50000000, 179930859/1000000000⟩
def contact1936 : RatBall := localContactBall tau1936 center1936
def work1936 : RoundedTauEval :=
  evalTau precision tau1936 contact1936 logTwoBall

theorem center_sq1936 : (center1936.re : ℝ)^2 +
    (center1936.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1936]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1936 : work1936.theta.ok = true ∧
    work1936.jac.invOK = true ∧ acceptsUnitSq work1936.out = true := by decide +kernel

def cell1936 : CellCertificate where
  tauBall := tau1936
  contactCenter := center1936
  contactBall := contact1936
  work := work1936
  center_sq := center_sq1936
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1936.1
  jac_ok := checks1936.2.1
  accepted := checks1936.2.2

def tau1937 : RatBall :=
  ⟨⟨-93/320, 89/320⟩, 3/640⟩
def center1937 : GaussianRat :=
  ⟨-84181/400000, 180208911/1000000000⟩
def contact1937 : RatBall := localContactBall tau1937 center1937
def work1937 : RoundedTauEval :=
  evalTau precision tau1937 contact1937 logTwoBall

theorem center_sq1937 : (center1937.re : ℝ)^2 +
    (center1937.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1937]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1937 : work1937.theta.ok = true ∧
    work1937.jac.invOK = true ∧ acceptsUnitSq work1937.out = true := by decide +kernel

def cell1937 : CellCertificate where
  tauBall := tau1937
  contactCenter := center1937
  contactBall := contact1937
  work := work1937
  center_sq := center_sq1937
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1937.1
  jac_ok := checks1937.2.1
  accepted := checks1937.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242


