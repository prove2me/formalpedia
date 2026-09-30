-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:52.822518+00:00
-- url     : https://prove2.me/theorems/32c40e07-4db5-47aa-a4f9-48a5a93a85f4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0117 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0936 : RatBall :=
  ⟨⟨-19/160, 47/160⟩, 3/320⟩
def center0936 : GaussianRat :=
  ⟨-89749431/1000000000, 206520639/1000000000⟩
def contact0936 : RatBall := localContactBall tau0936 center0936
def work0936 : RoundedTauEval :=
  evalTau precision tau0936 contact0936 logTwoBall

theorem center_sq0936 : (center0936.re : ℝ)^2 +
    (center0936.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0936]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0936 : work0936.theta.ok = true ∧
    work0936.jac.invOK = true ∧ acceptsUnitSq work0936.out = true := by decide +kernel

def cell0936 : CellCertificate where
  tauBall := tau0936
  contactCenter := center0936
  contactBall := contact0936
  work := work0936
  center_sq := center_sq0936
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0936.1
  jac_ok := checks0936.2.1
  accepted := checks0936.2.2

def tau0937 : RatBall :=
  ⟨⟨-17/160, 47/160⟩, 3/320⟩
def center0937 : GaussianRat :=
  ⟨-20104647/250000000, 10360657/50000000⟩
def contact0937 : RatBall := localContactBall tau0937 center0937
def work0937 : RoundedTauEval :=
  evalTau precision tau0937 contact0937 logTwoBall

theorem center_sq0937 : (center0937.re : ℝ)^2 +
    (center0937.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0937]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0937 : work0937.theta.ok = true ∧
    work0937.jac.invOK = true ∧ acceptsUnitSq work0937.out = true := by decide +kernel

def cell0937 : CellCertificate where
  tauBall := tau0937
  contactCenter := center0937
  contactBall := contact0937
  work := work0937
  center_sq := center_sq0937
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0937.1
  jac_ok := checks0937.2.1
  accepted := checks0937.2.2

def tau0938 : RatBall :=
  ⟨⟨-3/32, 9/32⟩, 3/320⟩
def center0938 : GaussianRat :=
  ⟨-17620809/250000000, 24810311/125000000⟩
def contact0938 : RatBall := localContactBall tau0938 center0938
def work0938 : RoundedTauEval :=
  evalTau precision tau0938 contact0938 logTwoBall

theorem center_sq0938 : (center0938.re : ℝ)^2 +
    (center0938.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0938]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0938 : work0938.theta.ok = true ∧
    work0938.jac.invOK = true ∧ acceptsUnitSq work0938.out = true := by decide +kernel

def cell0938 : CellCertificate where
  tauBall := tau0938
  contactCenter := center0938
  contactBall := contact0938
  work := work0938
  center_sq := center_sq0938
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0938.1
  jac_ok := checks0938.2.1
  accepted := checks0938.2.2

def tau0939 : RatBall :=
  ⟨⟨-13/160, 9/32⟩, 3/320⟩
def center0939 : GaussianRat :=
  ⟨-30576347/500000000, 99498463/500000000⟩
def contact0939 : RatBall := localContactBall tau0939 center0939
def work0939 : RoundedTauEval :=
  evalTau precision tau0939 contact0939 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117


