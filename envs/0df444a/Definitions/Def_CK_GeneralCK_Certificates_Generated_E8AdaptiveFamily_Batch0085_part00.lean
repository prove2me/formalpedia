-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0085_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0085_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:30.043889+00:00
-- url     : https://prove2.me/theorems/ffc5a06a-2275-4e18-8012-c1dc31af0385
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0085 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0680 : RatBall :=
  ⟨⟨47/160, -37/160⟩, 3/320⟩
def center0680 : GaussianRat :=
  ⟨103902067/500000000, -37194907/250000000⟩
def contact0680 : RatBall := localContactBall tau0680 center0680
def work0680 : RoundedTauEval :=
  evalTau precision tau0680 contact0680 logTwoBall

theorem center_sq0680 : (center0680.re : ℝ)^2 +
    (center0680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0680 : work0680.theta.ok = true ∧
    work0680.jac.invOK = true ∧ acceptsUnitSq work0680.out = true := by decide +kernel

def cell0680 : CellCertificate where
  tauBall := tau0680
  contactCenter := center0680
  contactBall := contact0680
  work := work0680
  center_sq := center_sq0680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0680.1
  jac_ok := checks0680.2.1
  accepted := checks0680.2.2

def tau0681 : RatBall :=
  ⟨⟨41/160, -7/32⟩, 3/320⟩
def center0681 : GaussianRat :=
  ⟨90907579/500000000, -143596387/1000000000⟩
def contact0681 : RatBall := localContactBall tau0681 center0681
def work0681 : RoundedTauEval :=
  evalTau precision tau0681 contact0681 logTwoBall

theorem center_sq0681 : (center0681.re : ℝ)^2 +
    (center0681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0681 : work0681.theta.ok = true ∧
    work0681.jac.invOK = true ∧ acceptsUnitSq work0681.out = true := by decide +kernel

def cell0681 : CellCertificate where
  tauBall := tau0681
  contactCenter := center0681
  contactBall := contact0681
  work := work0681
  center_sq := center_sq0681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0681.1
  jac_ok := checks0681.2.1
  accepted := checks0681.2.2

def tau0682 : RatBall :=
  ⟨⟨43/160, -7/32⟩, 3/320⟩
def center0682 : GaussianRat :=
  ⟨9509069/50000000, -71308977/500000000⟩
def contact0682 : RatBall := localContactBall tau0682 center0682
def work0682 : RoundedTauEval :=
  evalTau precision tau0682 contact0682 logTwoBall

theorem center_sq0682 : (center0682.re : ℝ)^2 +
    (center0682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0682 : work0682.theta.ok = true ∧
    work0682.jac.invOK = true ∧ acceptsUnitSq work0682.out = true := by decide +kernel

def cell0682 : CellCertificate where
  tauBall := tau0682
  contactCenter := center0682
  contactBall := contact0682
  work := work0682
  center_sq := center_sq0682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0682.1
  jac_ok := checks0682.2.1
  accepted := checks0682.2.2

def tau0683 : RatBall :=
  ⟨⟨41/160, -33/160⟩, 3/320⟩
def center0683 : GaussianRat :=
  ⟨180884951/1000000000, -135214257/1000000000⟩
def contact0683 : RatBall := localContactBall tau0683 center0683
def work0683 : RoundedTauEval :=
  evalTau precision tau0683 contact0683 logTwoBall

theorem center_sq0683 : (center0683.re : ℝ)^2 +
    (center0683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0683 : work0683.theta.ok = true ∧
    work0683.jac.invOK = true ∧ acceptsUnitSq work0683.out = true := by decide +kernel

def cell0683 : CellCertificate where
  tauBall := tau0683
  contactCenter := center0683
  contactBall := contact0683
  work := work0683
  center_sq := center_sq0683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0683.1
  jac_ok := checks0683.2.1
  accepted := checks0683.2.2

def tau0684 : RatBall :=
  ⟨⟨43/160, -33/160⟩, 3/320⟩
def center0684 : GaussianRat :=
  ⟨189219451/1000000000, -67150009/500000000⟩
def contact0684 : RatBall := localContactBall tau0684 center0684
def work0684 : RoundedTauEval :=
  evalTau precision tau0684 contact0684 logTwoBall

theorem center_sq0684 : (center0684.re : ℝ)^2 +
    (center0684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0684 : work0684.theta.ok = true ∧
    work0684.jac.invOK = true ∧ acceptsUnitSq work0684.out = true := by decide +kernel

def cell0684 : CellCertificate where
  tauBall := tau0684
  contactCenter := center0684
  contactBall := contact0684
  work := work0684
  center_sq := center_sq0684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0684.1
  jac_ok := checks0684.2.1
  accepted := checks0684.2.2

def tau0685 : RatBall :=
  ⟨⟨9/32, -7/32⟩, 3/320⟩
def center0685 : GaussianRat :=
  ⟨49620407/250000000, -141607653/1000000000⟩
def contact0685 : RatBall := localContactBall tau0685 center0685
def work0685 : RoundedTauEval :=
  evalTau precision tau0685 contact0685 logTwoBall

theorem center_sq0685 : (center0685.re : ℝ)^2 +
    (center0685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0685 : work0685.theta.ok = true ∧
    work0685.jac.invOK = true ∧ acceptsUnitSq work0685.out = true := by decide +kernel

def cell0685 : CellCertificate where
  tauBall := tau0685
  contactCenter := center0685
  contactBall := contact0685
  work := work0685
  center_sq := center_sq0685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0685.1
  jac_ok := checks0685.2.1
  accepted := checks0685.2.2

def tau0686 : RatBall :=
  ⟨⟨47/160, -7/32⟩, 3/320⟩
def center0686 : GaussianRat :=
  ⟨206714057/1000000000, -70283583/500000000⟩
def contact0686 : RatBall := localContactBall tau0686 center0686
def work0686 : RoundedTauEval :=
  evalTau precision tau0686 contact0686 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085


