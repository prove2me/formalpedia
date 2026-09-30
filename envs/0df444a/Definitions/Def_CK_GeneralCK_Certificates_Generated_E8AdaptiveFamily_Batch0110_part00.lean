-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0110_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:06:42.601542+00:00
-- url     : https://prove2.me/theorems/9739b583-b884-43dc-9223-82c35221386e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0110 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0880 : RatBall :=
  ⟨⟨-39/160, 39/160⟩, 3/320⟩
def center0880 : GaussianRat :=
  ⟨-7014647/40000000, 32307527/200000000⟩
def contact0880 : RatBall := localContactBall tau0880 center0880
def work0880 : RoundedTauEval :=
  evalTau precision tau0880 contact0880 logTwoBall

theorem center_sq0880 : (center0880.re : ℝ)^2 +
    (center0880.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0880]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0880 : work0880.theta.ok = true ∧
    work0880.jac.invOK = true ∧ acceptsUnitSq work0880.out = true := by decide +kernel

def cell0880 : CellCertificate where
  tauBall := tau0880
  contactCenter := center0880
  contactBall := contact0880
  work := work0880
  center_sq := center_sq0880
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0880.1
  jac_ok := checks0880.2.1
  accepted := checks0880.2.2

def tau0881 : RatBall :=
  ⟨⟨-37/160, 39/160⟩, 3/320⟩
def center0881 : GaussianRat :=
  ⟨-83398769/500000000, 20321547/125000000⟩
def contact0881 : RatBall := localContactBall tau0881 center0881
def work0881 : RoundedTauEval :=
  evalTau precision tau0881 contact0881 logTwoBall

theorem center_sq0881 : (center0881.re : ℝ)^2 +
    (center0881.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0881]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0881 : work0881.theta.ok = true ∧
    work0881.jac.invOK = true ∧ acceptsUnitSq work0881.out = true := by decide +kernel

def cell0881 : CellCertificate where
  tauBall := tau0881
  contactCenter := center0881
  contactBall := contact0881
  work := work0881
  center_sq := center_sq0881
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0881.1
  jac_ok := checks0881.2.1
  accepted := checks0881.2.2

def tau0882 : RatBall :=
  ⟨⟨-7/32, 37/160⟩, 3/320⟩
def center0882 : GaussianRat :=
  ⟨-78611951/500000000, 154924327/1000000000⟩
def contact0882 : RatBall := localContactBall tau0882 center0882

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110


