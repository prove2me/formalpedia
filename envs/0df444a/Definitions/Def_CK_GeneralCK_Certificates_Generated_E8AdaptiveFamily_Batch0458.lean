-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0458
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0458
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:26:18.84239+00:00
-- url     : https://prove2.me/theorems/25d63f5b-4068-49e2-ace2-6b311904819d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0458.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0458_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3670 : GaussianRat :=
  ⟨75128671/1000000000, 55898717/200000000⟩
def contact3670 : RatBall := localContactBall tau3670 center3670
def work3670 : RoundedTauEval :=
  evalTau precision tau3670 contact3670 logTwoBall

theorem center_sq3670 : (center3670.re : ℝ)^2 +
    (center3670.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3670]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3670 : work3670.theta.ok = true ∧
    work3670.jac.invOK = true ∧ acceptsUnitSq work3670.out = true := by decide +kernel

def cell3670 : CellCertificate where
  tauBall := tau3670
  contactCenter := center3670
  contactBall := contact3670
  work := work3670
  center_sq := center_sq3670
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3670.1
  jac_ok := checks3670.2.1
  accepted := checks3670.2.2

def tau3671 : RatBall :=
  ⟨⟨61/640, 49/128⟩, 3/1280⟩
def center3671 : GaussianRat :=
  ⟨3096871/40000000, 138381321/500000000⟩
def contact3671 : RatBall := localContactBall tau3671 center3671
def work3671 : RoundedTauEval :=
  evalTau precision tau3671 contact3671 logTwoBall

theorem center_sq3671 : (center3671.re : ℝ)^2 +
    (center3671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3671 : work3671.theta.ok = true ∧
    work3671.jac.invOK = true ∧ acceptsUnitSq work3671.out = true := by decide +kernel

def cell3671 : CellCertificate where
  tauBall := tau3671
  contactCenter := center3671
  contactBall := contact3671
  work := work3671
  center_sq := center_sq3671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3671.1
  jac_ok := checks3671.2.1
  accepted := checks3671.2.2

def cells : List CellCertificate := [cell3664, cell3665, cell3666, cell3667, cell3668, cell3669, cell3670, cell3671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458


