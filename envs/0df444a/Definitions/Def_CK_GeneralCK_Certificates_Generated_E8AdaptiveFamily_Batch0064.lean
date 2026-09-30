-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0064
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0064
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:23:35.786991+00:00
-- url     : https://prove2.me/theorems/b4094840-f574-49d4-bf11-54400728fa6b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0064.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0512 : RatBall :=
  ⟨⟨-59/160, -17/160⟩, 3/320⟩
def center0512 : GaussianRat :=
  ⟨-15424847/62500000, -32309019/500000000⟩
def contact0512 : RatBall := localContactBall tau0512 center0512
def work0512 : RoundedTauEval :=
  evalTau precision tau0512 contact0512 logTwoBall

theorem center_sq0512 : (center0512.re : ℝ)^2 +
    (center0512.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0512]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0512 : work0512.theta.ok = true ∧
    work0512.jac.invOK = true ∧ acceptsUnitSq work0512.out = true := by decide +kernel

def cell0512 : CellCertificate where
  tauBall := tau0512
  contactCenter := center0512
  contactBall := contact0512
  work := work0512
  center_sq := center_sq0512
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0512.1
  jac_ok := checks0512.2.1
  accepted := checks0512.2.2

def tau0513 : RatBall :=
  ⟨⟨-57/160, -17/160⟩, 3/320⟩
def center0513 : GaussianRat :=
  ⟨-119567729/500000000, -32582953/500000000⟩
def contact0513 : RatBall := localContactBall tau0513 center0513
def work0513 : RoundedTauEval :=
  evalTau precision tau0513 contact0513 logTwoBall

theorem center_sq0513 : (center0513.re : ℝ)^2 +
    (center0513.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0513]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0513 : work0513.theta.ok = true ∧
    work0513.jac.invOK = true ∧ acceptsUnitSq work0513.out = true := by decide +kernel

def cell0513 : CellCertificate where
  tauBall := tau0513
  contactCenter := center0513
  contactBall := contact0513
  work := work0513
  center_sq := center_sq0513
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0513.1
  jac_ok := checks0513.2.1
  accepted := checks0513.2.2

def tau0514 : RatBall :=
  ⟨⟨-11/32, -23/160⟩, 3/320⟩
def center0514 : GaussianRat :=
  ⟨-58324897/250000000, -11129939/125000000⟩
def contact0514 : RatBall := localContactBall tau0514 center0514
def work0514 : RoundedTauEval :=
  evalTau precision tau0514 contact0514 logTwoBall

theorem center_sq0514 : (center0514.re : ℝ)^2 +
    (center0514.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0514]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0514 : work0514.theta.ok = true ∧
    work0514.jac.invOK = true ∧ acceptsUnitSq work0514.out = true := by decide +kernel

def cell0514 : CellCertificate where
  tauBall := tau0514
  contactCenter := center0514
  contactBall := contact0514
  work := work0514
  center_sq := center_sq0514
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0514.1
  jac_ok := checks0514.2.1
  accepted := checks0514.2.2

def tau0515 : RatBall :=
  ⟨⟨-53/160, -23/160⟩, 3/320⟩
def center0515 : GaussianRat :=
  ⟨-225467593/1000000000, -89762261/1000000000⟩
def contact0515 : RatBall := localContactBall tau0515 center0515
def work0515 : RoundedTauEval :=
  evalTau precision tau0515 contact0515 logTwoBall

theorem center_sq0515 : (center0515.re : ℝ)^2 +
    (center0515.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0515]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0515 : work0515.theta.ok = true ∧
    work0515.jac.invOK = true ∧ acceptsUnitSq work0515.out = true := by decide +kernel

def cell0515 : CellCertificate where
  tauBall := tau0515
  contactCenter := center0515
  contactBall := contact0515
  work := work0515
  center_sq := center_sq0515
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0515.1
  jac_ok := checks0515.2.1
  accepted := checks0515.2.2

def tau0516 : RatBall :=
  ⟨⟨-11/32, -21/160⟩, 3/320⟩
def center0516 : GaussianRat :=
  ⟨-232602861/1000000000, -81248009/1000000000⟩
def contact0516 : RatBall := localContactBall tau0516 center0516
def work0516 : RoundedTauEval :=
  evalTau precision tau0516 contact0516 logTwoBall

theorem center_sq0516 : (center0516.re : ℝ)^2 +
    (center0516.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0516]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0516 : work0516.theta.ok = true ∧
    work0516.jac.invOK = true ∧ acceptsUnitSq work0516.out = true := by decide +kernel

def cell0516 : CellCertificate where
  tauBall := tau0516
  contactCenter := center0516
  contactBall := contact0516
  work := work0516
  center_sq := center_sq0516
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0516.1
  jac_ok := checks0516.2.1
  accepted := checks0516.2.2

def tau0517 : RatBall :=
  ⟨⟨-53/160, -21/160⟩, 3/320⟩
def center0517 : GaussianRat :=
  ⟨-224785281/1000000000, -4095231/50000000⟩
def contact0517 : RatBall := localContactBall tau0517 center0517
def work0517 : RoundedTauEval :=
  evalTau precision tau0517 contact0517 logTwoBall

theorem center_sq0517 : (center0517.re : ℝ)^2 +
    (center0517.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0517]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0517 : work0517.theta.ok = true ∧
    work0517.jac.invOK = true ∧ acceptsUnitSq work0517.out = true := by decide +kernel

def cell0517 : CellCertificate where
  tauBall := tau0517
  contactCenter := center0517
  contactBall := contact0517
  work := work0517
  center_sq := center_sq0517
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0517.1
  jac_ok := checks0517.2.1
  accepted := checks0517.2.2

def tau0518 : RatBall :=
  ⟨⟨-51/160, -23/160⟩, 3/320⟩
def center0518 : GaussianRat :=
  ⟨-6799051/31250000, -90469443/1000000000⟩
def contact0518 : RatBall := localContactBall tau0518 center0518
def work0518 : RoundedTauEval :=
  evalTau precision tau0518 contact0518 logTwoBall

theorem center_sq0518 : (center0518.re : ℝ)^2 +
    (center0518.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0518]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0518 : work0518.theta.ok = true ∧
    work0518.jac.invOK = true ∧ acceptsUnitSq work0518.out = true := by decide +kernel

def cell0518 : CellCertificate where
  tauBall := tau0518
  contactCenter := center0518
  contactBall := contact0518
  work := work0518
  center_sq := center_sq0518
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0518.1
  jac_ok := checks0518.2.1
  accepted := checks0518.2.2

def tau0519 : RatBall :=
  ⟨⟨-49/160, -23/160⟩, 3/320⟩
def center0519 : GaussianRat :=
  ⟨-209607093/1000000000, -22790011/250000000⟩
def contact0519 : RatBall := localContactBall tau0519 center0519
def work0519 : RoundedTauEval :=
  evalTau precision tau0519 contact0519 logTwoBall

theorem center_sq0519 : (center0519.re : ℝ)^2 +
    (center0519.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0519]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0519 : work0519.theta.ok = true ∧
    work0519.jac.invOK = true ∧ acceptsUnitSq work0519.out = true := by decide +kernel

def cell0519 : CellCertificate where
  tauBall := tau0519
  contactCenter := center0519
  contactBall := contact0519
  work := work0519
  center_sq := center_sq0519
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0519.1
  jac_ok := checks0519.2.1
  accepted := checks0519.2.2

def cells : List CellCertificate := [cell0512, cell0513, cell0514, cell0515, cell0516, cell0517, cell0518, cell0519]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064

end


