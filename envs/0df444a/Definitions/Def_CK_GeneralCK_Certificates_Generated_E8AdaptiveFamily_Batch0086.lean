-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:06:05.531089+00:00
-- url     : https://prove2.me/theorems/ee4c65b6-7cef-48ad-a116-2212f3270605
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0086.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0693 : work0693.theta.ok = true ∧
    work0693.jac.invOK = true ∧ acceptsUnitSq work0693.out = true := by decide +kernel

def cell0693 : CellCertificate where
  tauBall := tau0693
  contactCenter := center0693
  contactBall := contact0693
  work := work0693
  center_sq := center_sq0693
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0693.1
  jac_ok := checks0693.2.1
  accepted := checks0693.2.2

def tau0694 : RatBall :=
  ⟨⟨53/160, -33/160⟩, 3/320⟩
def center0694 : GaussianRat :=
  ⟨114945839/500000000, -32327639/250000000⟩
def contact0694 : RatBall := localContactBall tau0694 center0694
def work0694 : RoundedTauEval :=
  evalTau precision tau0694 contact0694 logTwoBall

theorem center_sq0694 : (center0694.re : ℝ)^2 +
    (center0694.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0694]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0694 : work0694.theta.ok = true ∧
    work0694.jac.invOK = true ∧ acceptsUnitSq work0694.out = true := by decide +kernel

def cell0694 : CellCertificate where
  tauBall := tau0694
  contactCenter := center0694
  contactBall := contact0694
  work := work0694
  center_sq := center_sq0694
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0694.1
  jac_ok := checks0694.2.1
  accepted := checks0694.2.2

def tau0695 : RatBall :=
  ⟨⟨37/160, -31/160⟩, 3/320⟩
def center0695 : GaussianRat :=
  ⟨163226979/1000000000, -128476919/1000000000⟩
def contact0695 : RatBall := localContactBall tau0695 center0695
def work0695 : RoundedTauEval :=
  evalTau precision tau0695 contact0695 logTwoBall

theorem center_sq0695 : (center0695.re : ℝ)^2 +
    (center0695.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0695]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0695 : work0695.theta.ok = true ∧
    work0695.jac.invOK = true ∧ acceptsUnitSq work0695.out = true := by decide +kernel

def cell0695 : CellCertificate where
  tauBall := tau0695
  contactCenter := center0695
  contactBall := contact0695
  work := work0695
  center_sq := center_sq0695
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0695.1
  jac_ok := checks0695.2.1
  accepted := checks0695.2.2

def cells : List CellCertificate := [cell0688, cell0689, cell0690, cell0691, cell0692, cell0693, cell0694, cell0695]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086


