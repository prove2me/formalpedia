-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:00.858063+00:00
-- url     : https://prove2.me/theorems/71ca088e-873e-4ba6-acee-64fcd4f506f4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0110 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0884 : CellCertificate where
  tauBall := tau0884
  contactCenter := center0884
  contactBall := contact0884
  work := work0884
  center_sq := center_sq0884
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0884.1
  jac_ok := checks0884.2.1
  accepted := checks0884.2.2

def tau0885 : RatBall :=
  ⟨⟨-33/160, 39/160⟩, 3/320⟩
def center0885 : GaussianRat :=
  ⟨-18684153/125000000, 164515579/1000000000⟩
def contact0885 : RatBall := localContactBall tau0885 center0885
def work0885 : RoundedTauEval :=
  evalTau precision tau0885 contact0885 logTwoBall

theorem center_sq0885 : (center0885.re : ℝ)^2 +
    (center0885.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0885]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0885 : work0885.theta.ok = true ∧
    work0885.jac.invOK = true ∧ acceptsUnitSq work0885.out = true := by decide +kernel

def cell0885 : CellCertificate where
  tauBall := tau0885
  contactCenter := center0885
  contactBall := contact0885
  work := work0885
  center_sq := center_sq0885
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0885.1
  jac_ok := checks0885.2.1
  accepted := checks0885.2.2

def tau0886 : RatBall :=
  ⟨⟨-43/160, 41/160⟩, 3/320⟩
def center0886 : GaussianRat :=
  ⟨-193470247/1000000000, 167770653/1000000000⟩
def contact0886 : RatBall := localContactBall tau0886 center0886
def work0886 : RoundedTauEval :=
  evalTau precision tau0886 contact0886 logTwoBall

theorem center_sq0886 : (center0886.re : ℝ)^2 +
    (center0886.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0886]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0886 : work0886.theta.ok = true ∧
    work0886.jac.invOK = true ∧ acceptsUnitSq work0886.out = true := by decide +kernel

def cell0886 : CellCertificate where
  tauBall := tau0886
  contactCenter := center0886
  contactBall := contact0886
  work := work0886
  center_sq := center_sq0886
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0886.1
  jac_ok := checks0886.2.1
  accepted := checks0886.2.2

def tau0887 : RatBall :=
  ⟨⟨-41/160, 41/160⟩, 3/320⟩
def center0887 : GaussianRat :=
  ⟨-184996961/1000000000, 21119029/125000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110


