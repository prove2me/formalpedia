-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:13:03.678679+00:00
-- url     : https://prove2.me/theorems/5cfa4fb8-87dc-4b0b-83ee-1cc2e51cc4dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0108 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0864 : RatBall :=
  ⟨⟨-9/32, 37/160⟩, 3/320⟩
def center0864 : GaussianRat :=
  ⟨-199541503/1000000000, 74944839/500000000⟩
def contact0864 : RatBall := localContactBall tau0864 center0864
def work0864 : RoundedTauEval :=
  evalTau precision tau0864 contact0864 logTwoBall

theorem center_sq0864 : (center0864.re : ℝ)^2 +
    (center0864.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0864]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0864 : work0864.theta.ok = true ∧
    work0864.jac.invOK = true ∧ acceptsUnitSq work0864.out = true := by decide +kernel

def cell0864 : CellCertificate where
  tauBall := tau0864
  contactCenter := center0864
  contactBall := contact0864
  work := work0864
  center_sq := center_sq0864
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0864.1
  jac_ok := checks0864.2.1
  accepted := checks0864.2.2

def tau0865 : RatBall :=
  ⟨⟨-9/32, 39/160⟩, 3/320⟩
def center0865 : GaussianRat :=
  ⟨-200670971/1000000000, 79101837/500000000⟩
def contact0865 : RatBall := localContactBall tau0865 center0865
def work0865 : RoundedTauEval :=
  evalTau precision tau0865 contact0865 logTwoBall

theorem center_sq0865 : (center0865.re : ℝ)^2 +
    (center0865.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0865]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0865 : work0865.theta.ok = true ∧
    work0865.jac.invOK = true ∧ acceptsUnitSq work0865.out = true := by decide +kernel

def cell0865 : CellCertificate where
  tauBall := tau0865
  contactCenter := center0865
  contactBall := contact0865
  work := work0865
  center_sq := center_sq0865
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0865.1
  jac_ok := checks0865.2.1
  accepted := checks0865.2.2

def tau0866 : RatBall :=
  ⟨⟨-43/160, 37/160⟩, 3/320⟩
def center0866 : GaussianRat :=
  ⟨-191209303/1000000000, 1887097/12500000⟩
def contact0866 : RatBall := localContactBall tau0866 center0866
def work0866 : RoundedTauEval :=
  evalTau precision tau0866 contact0866 logTwoBall

theorem center_sq0866 : (center0866.re : ℝ)^2 +
    (center0866.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0866]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0866 : work0866.theta.ok = true ∧
    work0866.jac.invOK = true ∧ acceptsUnitSq work0866.out = true := by decide +kernel

def cell0866 : CellCertificate where
  tauBall := tau0866
  contactCenter := center0866
  contactBall := contact0866
  work := work0866
  center_sq := center_sq0866
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0866.1
  jac_ok := checks0866.2.1
  accepted := checks0866.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108


