-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0149
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0149
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:27:48.225615+00:00
-- url     : https://prove2.me/theorems/f85f377c-be51-47c7-9145-772080536238
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0149.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0149_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1197 : work1197.theta.ok = true ∧
    work1197.jac.invOK = true ∧ acceptsUnitSq work1197.out = true := by decide +kernel

def cell1197 : CellCertificate where
  tauBall := tau1197
  contactCenter := center1197
  contactBall := contact1197
  work := work1197
  center_sq := center_sq1197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1197.1
  jac_ok := checks1197.2.1
  accepted := checks1197.2.2

def tau1198 : RatBall :=
  ⟨⟨53/160, 33/160⟩, 3/320⟩
def center1198 : GaussianRat :=
  ⟨114945839/500000000, 32327639/250000000⟩
def contact1198 : RatBall := localContactBall tau1198 center1198
def work1198 : RoundedTauEval :=
  evalTau precision tau1198 contact1198 logTwoBall

theorem center_sq1198 : (center1198.re : ℝ)^2 +
    (center1198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1198 : work1198.theta.ok = true ∧
    work1198.jac.invOK = true ∧ acceptsUnitSq work1198.out = true := by decide +kernel

def cell1198 : CellCertificate where
  tauBall := tau1198
  contactCenter := center1198
  contactBall := contact1198
  work := work1198
  center_sq := center_sq1198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1198.1
  jac_ok := checks1198.2.1
  accepted := checks1198.2.2

def tau1199 : RatBall :=
  ⟨⟨49/160, 37/160⟩, 3/320⟩
def center1199 : GaussianRat :=
  ⟨8639819/40000000, 36909857/250000000⟩
def contact1199 : RatBall := localContactBall tau1199 center1199
def work1199 : RoundedTauEval :=
  evalTau precision tau1199 contact1199 logTwoBall

theorem center_sq1199 : (center1199.re : ℝ)^2 +
    (center1199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1199 : work1199.theta.ok = true ∧
    work1199.jac.invOK = true ∧ acceptsUnitSq work1199.out = true := by decide +kernel

def cell1199 : CellCertificate where
  tauBall := tau1199
  contactCenter := center1199
  contactBall := contact1199
  work := work1199
  center_sq := center_sq1199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1199.1
  jac_ok := checks1199.2.1
  accepted := checks1199.2.2

def cells : List CellCertificate := [cell1192, cell1193, cell1194, cell1195, cell1196, cell1197, cell1198, cell1199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149


