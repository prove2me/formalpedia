-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:57.018788+00:00
-- url     : https://prove2.me/theorems/81025215-0210-45f9-a410-fcf215546054
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0104 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0832 : RatBall :=
  ⟨⟨-49/160, 31/160⟩, 3/320⟩
def center0832 : GaussianRat :=
  ⟨-106425859/500000000, 123294587/1000000000⟩
def contact0832 : RatBall := localContactBall tau0832 center0832
def work0832 : RoundedTauEval :=
  evalTau precision tau0832 contact0832 logTwoBall

theorem center_sq0832 : (center0832.re : ℝ)^2 +
    (center0832.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0832]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0832 : work0832.theta.ok = true ∧
    work0832.jac.invOK = true ∧ acceptsUnitSq work0832.out = true := by decide +kernel

def cell0832 : CellCertificate where
  tauBall := tau0832
  contactCenter := center0832
  contactBall := contact0832
  work := work0832
  center_sq := center_sq0832
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0832.1
  jac_ok := checks0832.2.1
  accepted := checks0832.2.2

def tau0833 : RatBall :=
  ⟨⟨-47/160, 5/32⟩, 3/320⟩
def center0833 : GaussianRat :=
  ⟨-202276259/1000000000, 49949641/500000000⟩
def contact0833 : RatBall := localContactBall tau0833 center0833
def work0833 : RoundedTauEval :=
  evalTau precision tau0833 contact0833 logTwoBall

theorem center_sq0833 : (center0833.re : ℝ)^2 +
    (center0833.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0833]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0833 : work0833.theta.ok = true ∧
    work0833.jac.invOK = true ∧ acceptsUnitSq work0833.out = true := by decide +kernel

def cell0833 : CellCertificate where
  tauBall := tau0833
  contactCenter := center0833
  contactBall := contact0833
  work := work0833
  center_sq := center_sq0833
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0833.1
  jac_ok := checks0833.2.1
  accepted := checks0833.2.2

def tau0834 : RatBall :=
  ⟨⟨-9/32, 5/32⟩, 3/320⟩
def center0834 : GaussianRat :=
  ⟨-194169161/1000000000, 100614871/1000000000⟩
def contact0834 : RatBall := localContactBall tau0834 center0834
def work0834 : RoundedTauEval :=
  evalTau precision tau0834 contact0834 logTwoBall

theorem center_sq0834 : (center0834.re : ℝ)^2 +
    (center0834.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0834]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0834 : work0834.theta.ok = true ∧
    work0834.jac.invOK = true ∧ acceptsUnitSq work0834.out = true := by decide +kernel

def cell0834 : CellCertificate where
  tauBall := tau0834
  contactCenter := center0834
  contactBall := contact0834
  work := work0834
  center_sq := center_sq0834
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0834.1
  jac_ok := checks0834.2.1
  accepted := checks0834.2.2

def tau0835 : RatBall :=
  ⟨⟨-47/160, 27/160⟩, 3/320⟩
def center0835 : GaussianRat :=
  ⟨-5075841/25000000, 107985769/1000000000⟩
def contact0835 : RatBall := localContactBall tau0835 center0835
def work0835 : RoundedTauEval :=
  evalTau precision tau0835 contact0835 logTwoBall

theorem center_sq0835 : (center0835.re : ℝ)^2 +
    (center0835.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0835]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0835 : work0835.theta.ok = true ∧
    work0835.jac.invOK = true ∧ acceptsUnitSq work0835.out = true := by decide +kernel

def cell0835 : CellCertificate where
  tauBall := tau0835
  contactCenter := center0835
  contactBall := contact0835
  work := work0835
  center_sq := center_sq0835
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0835.1
  jac_ok := checks0835.2.1
  accepted := checks0835.2.2

def tau0836 : RatBall :=
  ⟨⟨-9/32, 27/160⟩, 3/320⟩
def center0836 : GaussianRat :=
  ⟨-194904883/1000000000, 13595459/125000000⟩
def contact0836 : RatBall := localContactBall tau0836 center0836
def work0836 : RoundedTauEval :=
  evalTau precision tau0836 contact0836 logTwoBall

theorem center_sq0836 : (center0836.re : ℝ)^2 +
    (center0836.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0836]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104


