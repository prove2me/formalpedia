-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:31:47.000083+00:00
-- url     : https://prove2.me/theorems/4ba0b6a0-3899-47bb-8b70-4d7853077d66
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0092.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0092_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0742 : RatBall :=
  ⟨⟨53/160, -17/160⟩, 3/320⟩
def center0742 : GaussianRat :=
  ⟨44722969/200000000, -66230667/1000000000⟩
def contact0742 : RatBall := localContactBall tau0742 center0742
def work0742 : RoundedTauEval :=
  evalTau precision tau0742 contact0742 logTwoBall

theorem center_sq0742 : (center0742.re : ℝ)^2 +
    (center0742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0742 : work0742.theta.ok = true ∧
    work0742.jac.invOK = true ∧ acceptsUnitSq work0742.out = true := by decide +kernel

def cell0742 : CellCertificate where
  tauBall := tau0742
  contactCenter := center0742
  contactBall := contact0742
  work := work0742
  center_sq := center_sq0742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0742.1
  jac_ok := checks0742.2.1
  accepted := checks0742.2.2

def tau0743 : RatBall :=
  ⟨⟨11/32, -17/160⟩, 3/320⟩
def center0743 : GaussianRat :=
  ⟨57851871/250000000, -6570369/100000000⟩
def contact0743 : RatBall := localContactBall tau0743 center0743
def work0743 : RoundedTauEval :=
  evalTau precision tau0743 contact0743 logTwoBall

theorem center_sq0743 : (center0743.re : ℝ)^2 +
    (center0743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0743 : work0743.theta.ok = true ∧
    work0743.jac.invOK = true ∧ acceptsUnitSq work0743.out = true := by decide +kernel

def cell0743 : CellCertificate where
  tauBall := tau0743
  contactCenter := center0743
  contactBall := contact0743
  work := work0743
  center_sq := center_sq0743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0743.1
  jac_ok := checks0743.2.1
  accepted := checks0743.2.2

def cells : List CellCertificate := [cell0736, cell0737, cell0738, cell0739, cell0740, cell0741, cell0742, cell0743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092


