-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0140
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0140
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:29.576103+00:00
-- url     : https://prove2.me/theorems/34772bac-da57-4f28-a741-8211307b4242
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0140.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0140_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1126 : work1126.theta.ok = true ∧
    work1126.jac.invOK = true ∧ acceptsUnitSq work1126.out = true := by decide +kernel

def cell1126 : CellCertificate where
  tauBall := tau1126
  contactCenter := center1126
  contactBall := contact1126
  work := work1126
  center_sq := center_sq1126
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1126.1
  jac_ok := checks1126.2.1
  accepted := checks1126.2.2

def tau1127 : RatBall :=
  ⟨⟨9/160, 49/160⟩, 3/320⟩
def center1127 : GaussianRat :=
  ⟨43120523/1000000000, 109375967/500000000⟩
def contact1127 : RatBall := localContactBall tau1127 center1127
def work1127 : RoundedTauEval :=
  evalTau precision tau1127 contact1127 logTwoBall

theorem center_sq1127 : (center1127.re : ℝ)^2 +
    (center1127.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1127]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1127 : work1127.theta.ok = true ∧
    work1127.jac.invOK = true ∧ acceptsUnitSq work1127.out = true := by decide +kernel

def cell1127 : CellCertificate where
  tauBall := tau1127
  contactCenter := center1127
  contactBall := contact1127
  work := work1127
  center_sq := center_sq1127
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1127.1
  jac_ok := checks1127.2.1
  accepted := checks1127.2.2

def cells : List CellCertificate := [cell1120, cell1121, cell1122, cell1123, cell1124, cell1125, cell1126, cell1127]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140


