-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0468
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0468
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:57:45.869906+00:00
-- url     : https://prove2.me/theorems/60cda289-d7c2-4c3f-8606-16e96693de56
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0468.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0468_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3750 : work3750.theta.ok = true ∧
    work3750.jac.invOK = true ∧ acceptsUnitSq work3750.out = true := by decide +kernel

def cell3750 : CellCertificate where
  tauBall := tau3750
  contactCenter := center3750
  contactBall := contact3750
  work := work3750
  center_sq := center_sq3750
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3750.1
  jac_ok := checks3750.2.1
  accepted := checks3750.2.2

def tau3751 : RatBall :=
  ⟨⟨69/640, 241/640⟩, 3/1280⟩
def center3751 : GaussianRat :=
  ⟨10867009/125000000, 67712443/250000000⟩
def contact3751 : RatBall := localContactBall tau3751 center3751
def work3751 : RoundedTauEval :=
  evalTau precision tau3751 contact3751 logTwoBall

theorem center_sq3751 : (center3751.re : ℝ)^2 +
    (center3751.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3751]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3751 : work3751.theta.ok = true ∧
    work3751.jac.invOK = true ∧ acceptsUnitSq work3751.out = true := by decide +kernel

def cell3751 : CellCertificate where
  tauBall := tau3751
  contactCenter := center3751
  contactBall := contact3751
  work := work3751
  center_sq := center_sq3751
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3751.1
  jac_ok := checks3751.2.1
  accepted := checks3751.2.2

def cells : List CellCertificate := [cell3744, cell3745, cell3746, cell3747, cell3748, cell3749, cell3750, cell3751]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468


