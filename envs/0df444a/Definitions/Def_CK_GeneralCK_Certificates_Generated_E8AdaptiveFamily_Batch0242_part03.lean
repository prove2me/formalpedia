-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part03
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:23:26.887296+00:00
-- url     : https://prove2.me/theorems/f746d89e-bcfe-4b5e-a964-f8f8758c19c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 4 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 4 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 4 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242 (part 4 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0242 (part 4 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0242_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1942 : RatBall :=
  ⟨⟨-89/320, 93/320⟩, 3/640⟩
def center1942 : GaussianRat :=
  ⟨-50860061/250000000, 2969643/15625000⟩
def contact1942 : RatBall := localContactBall tau1942 center1942
def work1942 : RoundedTauEval :=
  evalTau precision tau1942 contact1942 logTwoBall

theorem center_sq1942 : (center1942.re : ℝ)^2 +
    (center1942.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1942]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1942 : work1942.theta.ok = true ∧
    work1942.jac.invOK = true ∧ acceptsUnitSq work1942.out = true := by decide +kernel

def cell1942 : CellCertificate where
  tauBall := tau1942
  contactCenter := center1942
  contactBall := contact1942
  work := work1942
  center_sq := center_sq1942
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1942.1
  jac_ok := checks1942.2.1
  accepted := checks1942.2.2

def tau1943 : RatBall :=
  ⟨⟨-87/320, 89/320⟩, 3/640⟩
def center1943 : GaussianRat :=
  ⟨-7912299/40000000, 91131277/500000000⟩
def contact1943 : RatBall := localContactBall tau1943 center1943
def work1943 : RoundedTauEval :=
  evalTau precision tau1943 contact1943 logTwoBall

theorem center_sq1943 : (center1943.re : ℝ)^2 +
    (center1943.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1943]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1943 : work1943.theta.ok = true ∧
    work1943.jac.invOK = true ∧ acceptsUnitSq work1943.out = true := by decide +kernel

def cell1943 : CellCertificate where
  tauBall := tau1943
  contactCenter := center1943
  contactBall := contact1943
  work := work1943
  center_sq := center_sq1943
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1943.1
  jac_ok := checks1943.2.1
  accepted := checks1943.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242


