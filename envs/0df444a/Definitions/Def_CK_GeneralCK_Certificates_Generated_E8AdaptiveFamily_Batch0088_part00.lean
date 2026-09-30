-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:18:28.823256+00:00
-- url     : https://prove2.me/theorems/c3de1bd9-ab30-4de0-ae5d-bf95500cdc79
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0088 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0704 : RatBall :=
  ⟨⟨47/160, -31/160⟩, 3/320⟩
def center0704 : GaussianRat :=
  ⟨40948189/200000000, -124226081/1000000000⟩
def contact0704 : RatBall := localContactBall tau0704 center0704
def work0704 : RoundedTauEval :=
  evalTau precision tau0704 contact0704 logTwoBall

theorem center_sq0704 : (center0704.re : ℝ)^2 +
    (center0704.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0704]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0704 : work0704.theta.ok = true ∧
    work0704.jac.invOK = true ∧ acceptsUnitSq work0704.out = true := by decide +kernel

def cell0704 : CellCertificate where
  tauBall := tau0704
  contactCenter := center0704
  contactBall := contact0704
  work := work0704
  center_sq := center_sq0704
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0704.1
  jac_ok := checks0704.2.1
  accepted := checks0704.2.2

def tau0705 : RatBall :=
  ⟨⟨9/32, -29/160⟩, 3/320⟩
def center0705 : GaussianRat :=
  ⟨97851331/500000000, -116935591/1000000000⟩
def contact0705 : RatBall := localContactBall tau0705 center0705
def work0705 : RoundedTauEval :=
  evalTau precision tau0705 contact0705 logTwoBall

theorem center_sq0705 : (center0705.re : ℝ)^2 +
    (center0705.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0705]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0705 : work0705.theta.ok = true ∧
    work0705.jac.invOK = true ∧ acceptsUnitSq work0705.out = true := by decide +kernel

def cell0705 : CellCertificate where
  tauBall := tau0705
  contactCenter := center0705
  contactBall := contact0705
  work := work0705
  center_sq := center_sq0705
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0705.1
  jac_ok := checks0705.2.1
  accepted := checks0705.2.2

def tau0706 : RatBall :=
  ⟨⟨47/160, -29/160⟩, 3/320⟩
def center0706 : GaussianRat :=
  ⟨25481847/125000000, -58047077/500000000⟩
def contact0706 : RatBall := localContactBall tau0706 center0706
def work0706 : RoundedTauEval :=
  evalTau precision tau0706 contact0706 logTwoBall

theorem center_sq0706 : (center0706.re : ℝ)^2 +
    (center0706.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0706]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0706 : work0706.theta.ok = true ∧
    work0706.jac.invOK = true ∧ acceptsUnitSq work0706.out = true := by decide +kernel

def cell0706 : CellCertificate where
  tauBall := tau0706
  contactCenter := center0706
  contactBall := contact0706
  work := work0706
  center_sq := center_sq0706
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0706.1
  jac_ok := checks0706.2.1
  accepted := checks0706.2.2

def tau0707 : RatBall :=
  ⟨⟨9/32, -27/160⟩, 3/320⟩
def center0707 : GaussianRat :=
  ⟨194904883/1000000000, -13595459/125000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088


