-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0067
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0067
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:40:18.037451+00:00
-- url     : https://prove2.me/theorems/6039bc28-9c3e-461e-9968-282aae73a9b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0067.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0536 : RatBall :=
  ⟨⟨-47/160, -5/32⟩, 3/320⟩
def center0536 : GaussianRat :=
  ⟨-202276259/1000000000, -49949641/500000000⟩
def contact0536 : RatBall := localContactBall tau0536 center0536
def work0536 : RoundedTauEval :=
  evalTau precision tau0536 contact0536 logTwoBall

theorem center_sq0536 : (center0536.re : ℝ)^2 +
    (center0536.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0536]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0536 : work0536.theta.ok = true ∧
    work0536.jac.invOK = true ∧ acceptsUnitSq work0536.out = true := by decide +kernel

def cell0536 : CellCertificate where
  tauBall := tau0536
  contactCenter := center0536
  contactBall := contact0536
  work := work0536
  center_sq := center_sq0536
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0536.1
  jac_ok := checks0536.2.1
  accepted := checks0536.2.2

def tau0537 : RatBall :=
  ⟨⟨-9/32, -5/32⟩, 3/320⟩
def center0537 : GaussianRat :=
  ⟨-194169161/1000000000, -100614871/1000000000⟩
def contact0537 : RatBall := localContactBall tau0537 center0537
def work0537 : RoundedTauEval :=
  evalTau precision tau0537 contact0537 logTwoBall

theorem center_sq0537 : (center0537.re : ℝ)^2 +
    (center0537.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0537]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0537 : work0537.theta.ok = true ∧
    work0537.jac.invOK = true ∧ acceptsUnitSq work0537.out = true := by decide +kernel

def cell0537 : CellCertificate where
  tauBall := tau0537
  contactCenter := center0537
  contactBall := contact0537
  work := work0537
  center_sq := center_sq0537
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0537.1
  jac_ok := checks0537.2.1
  accepted := checks0537.2.2

def tau0538 : RatBall :=
  ⟨⟨-39/160, -31/160⟩, 3/320⟩
def center0538 : GaussianRat :=
  ⟨-10728219/62500000, -127685733/1000000000⟩
def contact0538 : RatBall := localContactBall tau0538 center0538
def work0538 : RoundedTauEval :=
  evalTau precision tau0538 contact0538 logTwoBall

theorem center_sq0538 : (center0538.re : ℝ)^2 +
    (center0538.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0538]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0538 : work0538.theta.ok = true ∧
    work0538.jac.invOK = true ∧ acceptsUnitSq work0538.out = true := by decide +kernel

def cell0538 : CellCertificate where
  tauBall := tau0538
  contactCenter := center0538
  contactBall := contact0538
  work := work0538
  center_sq := center_sq0538
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0538.1
  jac_ok := checks0538.2.1
  accepted := checks0538.2.2

def tau0539 : RatBall :=
  ⟨⟨-37/160, -31/160⟩, 3/320⟩
def center0539 : GaussianRat :=
  ⟨-163226979/1000000000, -128476919/1000000000⟩
def contact0539 : RatBall := localContactBall tau0539 center0539
def work0539 : RoundedTauEval :=
  evalTau precision tau0539 contact0539 logTwoBall

theorem center_sq0539 : (center0539.re : ℝ)^2 +
    (center0539.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0539]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0539 : work0539.theta.ok = true ∧
    work0539.jac.invOK = true ∧ acceptsUnitSq work0539.out = true := by decide +kernel

def cell0539 : CellCertificate where
  tauBall := tau0539
  contactCenter := center0539
  contactBall := contact0539
  work := work0539
  center_sq := center_sq0539
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0539.1
  jac_ok := checks0539.2.1
  accepted := checks0539.2.2

def tau0540 : RatBall :=
  ⟨⟨-39/160, -29/160⟩, 3/320⟩
def center0540 : GaussianRat :=
  ⟨-2135923/12500000, -119305389/1000000000⟩
def contact0540 : RatBall := localContactBall tau0540 center0540
def work0540 : RoundedTauEval :=
  evalTau precision tau0540 contact0540 logTwoBall

theorem center_sq0540 : (center0540.re : ℝ)^2 +
    (center0540.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0540]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0540 : work0540.theta.ok = true ∧
    work0540.jac.invOK = true ∧ acceptsUnitSq work0540.out = true := by decide +kernel

def cell0540 : CellCertificate where
  tauBall := tau0540
  contactCenter := center0540
  contactBall := contact0540
  work := work0540
  center_sq := center_sq0540
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0540.1
  jac_ok := checks0540.2.1
  accepted := checks0540.2.2

def tau0541 : RatBall :=
  ⟨⟨-37/160, -29/160⟩, 3/320⟩
def center0541 : GaussianRat :=
  ⟨-81239917/500000000, -60019727/500000000⟩
def contact0541 : RatBall := localContactBall tau0541 center0541
def work0541 : RoundedTauEval :=
  evalTau precision tau0541 contact0541 logTwoBall

theorem center_sq0541 : (center0541.re : ℝ)^2 +
    (center0541.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0541]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0541 : work0541.theta.ok = true ∧
    work0541.jac.invOK = true ∧ acceptsUnitSq work0541.out = true := by decide +kernel

def cell0541 : CellCertificate where
  tauBall := tau0541
  contactCenter := center0541
  contactBall := contact0541
  work := work0541
  center_sq := center_sq0541
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0541.1
  jac_ok := checks0541.2.1
  accepted := checks0541.2.2

def tau0542 : RatBall :=
  ⟨⟨-63/160, -3/32⟩, 3/320⟩
def center0542 : GaussianRat :=
  ⟨-65346019/250000000, -28003013/500000000⟩
def contact0542 : RatBall := localContactBall tau0542 center0542
def work0542 : RoundedTauEval :=
  evalTau precision tau0542 contact0542 logTwoBall

theorem center_sq0542 : (center0542.re : ℝ)^2 +
    (center0542.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0542]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0542 : work0542.theta.ok = true ∧
    work0542.jac.invOK = true ∧ acceptsUnitSq work0542.out = true := by decide +kernel

def cell0542 : CellCertificate where
  tauBall := tau0542
  contactCenter := center0542
  contactBall := contact0542
  work := work0542
  center_sq := center_sq0542
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0542.1
  jac_ok := checks0542.2.1
  accepted := checks0542.2.2

def tau0543 : RatBall :=
  ⟨⟨-61/160, -3/32⟩, 3/320⟩
def center0543 : GaussianRat :=
  ⟨-50772973/200000000, -14125933/250000000⟩
def contact0543 : RatBall := localContactBall tau0543 center0543
def work0543 : RoundedTauEval :=
  evalTau precision tau0543 contact0543 logTwoBall

theorem center_sq0543 : (center0543.re : ℝ)^2 +
    (center0543.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0543]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0543 : work0543.theta.ok = true ∧
    work0543.jac.invOK = true ∧ acceptsUnitSq work0543.out = true := by decide +kernel

def cell0543 : CellCertificate where
  tauBall := tau0543
  contactCenter := center0543
  contactBall := contact0543
  work := work0543
  center_sq := center_sq0543
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0543.1
  jac_ok := checks0543.2.1
  accepted := checks0543.2.2

def cells : List CellCertificate := [cell0536, cell0537, cell0538, cell0539, cell0540, cell0541, cell0542, cell0543]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067

end


