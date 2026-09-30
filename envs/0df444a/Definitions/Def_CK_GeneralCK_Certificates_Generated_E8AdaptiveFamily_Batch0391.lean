-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:01:51.140283+00:00
-- url     : https://prove2.me/theorems/d5e151dc-c0ca-4b43-bf44-8314eb6010d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0391.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0391_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3134 : RoundedTauEval :=
  evalTau precision tau3134 contact3134 logTwoBall

theorem center_sq3134 : (center3134.re : ℝ)^2 +
    (center3134.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3134]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3134 : work3134.theta.ok = true ∧
    work3134.jac.invOK = true ∧ acceptsUnitSq work3134.out = true := by decide +kernel

def cell3134 : CellCertificate where
  tauBall := tau3134
  contactCenter := center3134
  contactBall := contact3134
  work := work3134
  center_sq := center_sq3134
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3134.1
  jac_ok := checks3134.2.1
  accepted := checks3134.2.2

def tau3135 : RatBall :=
  ⟨⟨97/640, -47/128⟩, 3/1280⟩
def center3135 : GaussianRat :=
  ⟨15043717/125000000, -259604029/1000000000⟩
def contact3135 : RatBall := localContactBall tau3135 center3135
def work3135 : RoundedTauEval :=
  evalTau precision tau3135 contact3135 logTwoBall

theorem center_sq3135 : (center3135.re : ℝ)^2 +
    (center3135.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3135]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3135 : work3135.theta.ok = true ∧
    work3135.jac.invOK = true ∧ acceptsUnitSq work3135.out = true := by decide +kernel

def cell3135 : CellCertificate where
  tauBall := tau3135
  contactCenter := center3135
  contactBall := contact3135
  work := work3135
  center_sq := center_sq3135
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3135.1
  jac_ok := checks3135.2.1
  accepted := checks3135.2.2

def cells : List CellCertificate := [cell3128, cell3129, cell3130, cell3131, cell3132, cell3133, cell3134, cell3135]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391


