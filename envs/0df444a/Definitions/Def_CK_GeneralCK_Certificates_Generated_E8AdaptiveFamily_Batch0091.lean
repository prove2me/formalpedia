-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0091
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0091
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:45:59.081023+00:00
-- url     : https://prove2.me/theorems/3acc6056-adc0-47a8-8c6b-0ff64f5e47ab
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0091.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0091_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0733 : work0733.theta.ok = true ∧
    work0733.jac.invOK = true ∧ acceptsUnitSq work0733.out = true := by decide +kernel

def cell0733 : CellCertificate where
  tauBall := tau0733
  contactCenter := center0733
  contactBall := contact0733
  work := work0733
  center_sq := center_sq0733
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0733.1
  jac_ok := checks0733.2.1
  accepted := checks0733.2.2

def tau0734 : RatBall :=
  ⟨⟨49/160, -21/160⟩, 3/320⟩
def center0734 : GaussianRat :=
  ⟨41791301/200000000, -41587123/500000000⟩
def contact0734 : RatBall := localContactBall tau0734 center0734
def work0734 : RoundedTauEval :=
  evalTau precision tau0734 contact0734 logTwoBall

theorem center_sq0734 : (center0734.re : ℝ)^2 +
    (center0734.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0734]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0734 : work0734.theta.ok = true ∧
    work0734.jac.invOK = true ∧ acceptsUnitSq work0734.out = true := by decide +kernel

def cell0734 : CellCertificate where
  tauBall := tau0734
  contactCenter := center0734
  contactBall := contact0734
  work := work0734
  center_sq := center_sq0734
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0734.1
  jac_ok := checks0734.2.1
  accepted := checks0734.2.2

def tau0735 : RatBall :=
  ⟨⟨51/160, -21/160⟩, 3/320⟩
def center0735 : GaussianRat :=
  ⟨216902699/1000000000, -20636751/250000000⟩
def contact0735 : RatBall := localContactBall tau0735 center0735
def work0735 : RoundedTauEval :=
  evalTau precision tau0735 contact0735 logTwoBall

theorem center_sq0735 : (center0735.re : ℝ)^2 +
    (center0735.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0735]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0735 : work0735.theta.ok = true ∧
    work0735.jac.invOK = true ∧ acceptsUnitSq work0735.out = true := by decide +kernel

def cell0735 : CellCertificate where
  tauBall := tau0735
  contactCenter := center0735
  contactBall := contact0735
  work := work0735
  center_sq := center_sq0735
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0735.1
  jac_ok := checks0735.2.1
  accepted := checks0735.2.2

def cells : List CellCertificate := [cell0728, cell0729, cell0730, cell0731, cell0732, cell0733, cell0734, cell0735]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091


