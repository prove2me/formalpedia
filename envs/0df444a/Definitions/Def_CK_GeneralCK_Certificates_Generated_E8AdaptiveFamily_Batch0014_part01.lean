-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0014_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0014_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:36:23.435035+00:00
-- url     : https://prove2.me/theorems/9a630b62-382c-49c7-a047-b59a4f2932ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0014 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0014_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0115 : CellCertificate where
  tauBall := tau0115
  contactCenter := center0115
  contactBall := contact0115
  work := work0115
  center_sq := center_sq0115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0115.1
  jac_ok := checks0115.2.1
  accepted := checks0115.2.2

def tau0116 : RatBall :=
  ⟨⟨-9/80, -13/80⟩, 3/160⟩
def center0116 : GaussianRat :=
  ⟨-79781827/1000000000, -56070187/500000000⟩
def contact0116 : RatBall := localContactBall tau0116 center0116
def work0116 : RoundedTauEval :=
  evalTau precision tau0116 contact0116 logTwoBall

theorem center_sq0116 : (center0116.re : ℝ)^2 +
    (center0116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0116 : work0116.theta.ok = true ∧
    work0116.jac.invOK = true ∧ acceptsUnitSq work0116.out = true := by decide +kernel

def cell0116 : CellCertificate where
  tauBall := tau0116
  contactCenter := center0116
  contactBall := contact0116
  work := work0116
  center_sq := center_sq0116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0116.1
  jac_ok := checks0116.2.1
  accepted := checks0116.2.2

def tau0117 : RatBall :=
  ⟨⟨-3/16, -11/80⟩, 3/160⟩
def center0117 : GaussianRat :=
  ⟨-130837509/1000000000, -92449971/1000000000⟩
def contact0117 : RatBall := localContactBall tau0117 center0117
def work0117 : RoundedTauEval :=
  evalTau precision tau0117 contact0117 logTwoBall

theorem center_sq0117 : (center0117.re : ℝ)^2 +
    (center0117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0117 : work0117.theta.ok = true ∧
    work0117.jac.invOK = true ∧ acceptsUnitSq work0117.out = true := by decide +kernel

def cell0117 : CellCertificate where
  tauBall := tau0117
  contactCenter := center0117
  contactBall := contact0117
  work := work0117
  center_sq := center_sq0117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0117.1
  jac_ok := checks0117.2.1
  accepted := checks0117.2.2

def tau0118 : RatBall :=
  ⟨⟨-13/80, -11/80⟩, 3/160⟩
def center0118 : GaussianRat :=
  ⟨-22751869/200000000, -46647191/500000000⟩
def contact0118 : RatBall := localContactBall tau0118 center0118
def work0118 : RoundedTauEval :=
  evalTau precision tau0118 contact0118 logTwoBall

theorem center_sq0118 : (center0118.re : ℝ)^2 +
    (center0118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0118 : work0118.theta.ok = true ∧
    work0118.jac.invOK = true ∧ acceptsUnitSq work0118.out = true := by decide +kernel

def cell0118 : CellCertificate where
  tauBall := tau0118
  contactCenter := center0118
  contactBall := contact0118
  work := work0118
  center_sq := center_sq0118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0118.1
  jac_ok := checks0118.2.1
  accepted := checks0118.2.2

def tau0119 : RatBall :=
  ⟨⟨-3/16, -9/80⟩, 3/160⟩
def center0119 : GaussianRat :=
  ⟨-26005447/200000000, -37751763/500000000⟩
def contact0119 : RatBall := localContactBall tau0119 center0119
def work0119 : RoundedTauEval :=
  evalTau precision tau0119 contact0119 logTwoBall

theorem center_sq0119 : (center0119.re : ℝ)^2 +
    (center0119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0119]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014


