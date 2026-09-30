-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:13:05.369051+00:00
-- url     : https://prove2.me/theorems/f2ac1fe0-0e85-460a-bc2d-2d940ae6be38
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0117 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0939 : (center0939.re : ℝ)^2 +
    (center0939.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0939]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0939 : work0939.theta.ok = true ∧
    work0939.jac.invOK = true ∧ acceptsUnitSq work0939.out = true := by decide +kernel

def cell0939 : CellCertificate where
  tauBall := tau0939
  contactCenter := center0939
  contactBall := contact0939
  work := work0939
  center_sq := center_sq0939
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0939.1
  jac_ok := checks0939.2.1
  accepted := checks0939.2.2

def tau0940 : RatBall :=
  ⟨⟨-3/32, 47/160⟩, 3/320⟩
def center0940 : GaussianRat :=
  ⟨-71049459/1000000000, 207833009/1000000000⟩
def contact0940 : RatBall := localContactBall tau0940 center0940
def work0940 : RoundedTauEval :=
  evalTau precision tau0940 contact0940 logTwoBall

theorem center_sq0940 : (center0940.re : ℝ)^2 +
    (center0940.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0940]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0940 : work0940.theta.ok = true ∧
    work0940.jac.invOK = true ∧ acceptsUnitSq work0940.out = true := by decide +kernel

def cell0940 : CellCertificate where
  tauBall := tau0940
  contactCenter := center0940
  contactBall := contact0940
  work := work0940
  center_sq := center_sq0940
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0940.1
  jac_ok := checks0940.2.1
  accepted := checks0940.2.2

def tau0941 : RatBall :=
  ⟨⟨-13/160, 47/160⟩, 3/320⟩
def center0941 : GaussianRat :=
  ⟨-61646237/1000000000, 5209469/25000000⟩
def contact0941 : RatBall := localContactBall tau0941 center0941
def work0941 : RoundedTauEval :=
  evalTau precision tau0941 contact0941 logTwoBall

theorem center_sq0941 : (center0941.re : ℝ)^2 +
    (center0941.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0941]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0941 : work0941.theta.ok = true ∧
    work0941.jac.invOK = true ∧ acceptsUnitSq work0941.out = true := by decide +kernel

def cell0941 : CellCertificate where
  tauBall := tau0941
  contactCenter := center0941
  contactBall := contact0941
  work := work0941
  center_sq := center_sq0941
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0941.1
  jac_ok := checks0941.2.1
  accepted := checks0941.2.2

def tau0942 : RatBall :=
  ⟨⟨-11/160, 9/32⟩, 3/320⟩
def center0942 : GaussianRat :=
  ⟨-25896777/500000000, 199440199/1000000000⟩
def contact0942 : RatBall := localContactBall tau0942 center0942
def work0942 : RoundedTauEval :=
  evalTau precision tau0942 contact0942 logTwoBall

theorem center_sq0942 : (center0942.re : ℝ)^2 +
    (center0942.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0942]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0942 : work0942.theta.ok = true ∧
    work0942.jac.invOK = true ∧ acceptsUnitSq work0942.out = true := by decide +kernel

def cell0942 : CellCertificate where
  tauBall := tau0942
  contactCenter := center0942
  contactBall := contact0942
  work := work0942
  center_sq := center_sq0942
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0942.1
  jac_ok := checks0942.2.1
  accepted := checks0942.2.2

def tau0943 : RatBall :=
  ⟨⟨-9/160, 9/32⟩, 3/320⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117


