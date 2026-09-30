-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0044
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0044
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:56:25.404484+00:00
-- url     : https://prove2.me/theorems/e983bd0c-bb11-4d4f-a31a-8e0e9bc593e3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0044.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0352 : RatBall :=
  ⟨⟨-7/32, -9/32⟩, 3/320⟩
def center0352 : GaussianRat :=
  ⟨-32272717/200000000, -189759799/1000000000⟩
def contact0352 : RatBall := localContactBall tau0352 center0352
def work0352 : RoundedTauEval :=
  evalTau precision tau0352 contact0352 logTwoBall

theorem center_sq0352 : (center0352.re : ℝ)^2 +
    (center0352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0352 : work0352.theta.ok = true ∧
    work0352.jac.invOK = true ∧ acceptsUnitSq work0352.out = true := by decide +kernel

def cell0352 : CellCertificate where
  tauBall := tau0352
  contactCenter := center0352
  contactBall := contact0352
  work := work0352
  center_sq := center_sq0352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0352.1
  jac_ok := checks0352.2.1
  accepted := checks0352.2.2

def tau0353 : RatBall :=
  ⟨⟨-33/160, -9/32⟩, 3/320⟩
def center0353 : GaussianRat :=
  ⟨-9532907/62500000, -95448491/500000000⟩
def contact0353 : RatBall := localContactBall tau0353 center0353
def work0353 : RoundedTauEval :=
  evalTau precision tau0353 contact0353 logTwoBall

theorem center_sq0353 : (center0353.re : ℝ)^2 +
    (center0353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0353 : work0353.theta.ok = true ∧
    work0353.jac.invOK = true ∧ acceptsUnitSq work0353.out = true := by decide +kernel

def cell0353 : CellCertificate where
  tauBall := tau0353
  contactCenter := center0353
  contactBall := contact0353
  work := work0353
  center_sq := center_sq0353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0353.1
  jac_ok := checks0353.2.1
  accepted := checks0353.2.2

def tau0354 : RatBall :=
  ⟨⟨-39/160, -43/160⟩, 3/320⟩
def center0354 : GaussianRat :=
  ⟨-177609433/1000000000, -178692329/1000000000⟩
def contact0354 : RatBall := localContactBall tau0354 center0354
def work0354 : RoundedTauEval :=
  evalTau precision tau0354 contact0354 logTwoBall

theorem center_sq0354 : (center0354.re : ℝ)^2 +
    (center0354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0354 : work0354.theta.ok = true ∧
    work0354.jac.invOK = true ∧ acceptsUnitSq work0354.out = true := by decide +kernel

def cell0354 : CellCertificate where
  tauBall := tau0354
  contactCenter := center0354
  contactBall := contact0354
  work := work0354
  center_sq := center_sq0354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0354.1
  jac_ok := checks0354.2.1
  accepted := checks0354.2.2

def tau0355 : RatBall :=
  ⟨⟨-37/160, -43/160⟩, 3/320⟩
def center0355 : GaussianRat :=
  ⟨-84477561/500000000, -89929857/500000000⟩
def contact0355 : RatBall := localContactBall tau0355 center0355
def work0355 : RoundedTauEval :=
  evalTau precision tau0355 contact0355 logTwoBall

theorem center_sq0355 : (center0355.re : ℝ)^2 +
    (center0355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0355 : work0355.theta.ok = true ∧
    work0355.jac.invOK = true ∧ acceptsUnitSq work0355.out = true := by decide +kernel

def cell0355 : CellCertificate where
  tauBall := tau0355
  contactCenter := center0355
  contactBall := contact0355
  work := work0355
  center_sq := center_sq0355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0355.1
  jac_ok := checks0355.2.1
  accepted := checks0355.2.2

def tau0356 : RatBall :=
  ⟨⟨-39/160, -41/160⟩, 3/320⟩
def center0356 : GaussianRat :=
  ⟨-44113519/250000000, -170094077/1000000000⟩
def contact0356 : RatBall := localContactBall tau0356 center0356
def work0356 : RoundedTauEval :=
  evalTau precision tau0356 contact0356 logTwoBall

theorem center_sq0356 : (center0356.re : ℝ)^2 +
    (center0356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0356 : work0356.theta.ok = true ∧
    work0356.jac.invOK = true ∧ acceptsUnitSq work0356.out = true := by decide +kernel

def cell0356 : CellCertificate where
  tauBall := tau0356
  contactCenter := center0356
  contactBall := contact0356
  work := work0356
  center_sq := center_sq0356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0356.1
  jac_ok := checks0356.2.1
  accepted := checks0356.2.2

def tau0357 : RatBall :=
  ⟨⟨-37/160, -41/160⟩, 3/320⟩
def center0357 : GaussianRat :=
  ⟨-167843761/1000000000, -171194117/1000000000⟩
def contact0357 : RatBall := localContactBall tau0357 center0357
def work0357 : RoundedTauEval :=
  evalTau precision tau0357 contact0357 logTwoBall

theorem center_sq0357 : (center0357.re : ℝ)^2 +
    (center0357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0357 : work0357.theta.ok = true ∧
    work0357.jac.invOK = true ∧ acceptsUnitSq work0357.out = true := by decide +kernel

def cell0357 : CellCertificate where
  tauBall := tau0357
  contactCenter := center0357
  contactBall := contact0357
  work := work0357
  center_sq := center_sq0357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0357.1
  jac_ok := checks0357.2.1
  accepted := checks0357.2.2

def tau0358 : RatBall :=
  ⟨⟨-7/32, -43/160⟩, 3/320⟩
def center0358 : GaussianRat :=
  ⟨-160233593/1000000000, -180980837/1000000000⟩
def contact0358 : RatBall := localContactBall tau0358 center0358
def work0358 : RoundedTauEval :=
  evalTau precision tau0358 contact0358 logTwoBall

theorem center_sq0358 : (center0358.re : ℝ)^2 +
    (center0358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0358 : work0358.theta.ok = true ∧
    work0358.jac.invOK = true ∧ acceptsUnitSq work0358.out = true := by decide +kernel

def cell0358 : CellCertificate where
  tauBall := tau0358
  contactCenter := center0358
  contactBall := contact0358
  work := work0358
  center_sq := center_sq0358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0358.1
  jac_ok := checks0358.2.1
  accepted := checks0358.2.2

def tau0359 : RatBall :=
  ⟨⟨-33/160, -43/160⟩, 3/320⟩
def center0359 : GaussianRat :=
  ⟨-151447357/1000000000, -91026767/500000000⟩
def contact0359 : RatBall := localContactBall tau0359 center0359
def work0359 : RoundedTauEval :=
  evalTau precision tau0359 contact0359 logTwoBall

theorem center_sq0359 : (center0359.re : ℝ)^2 +
    (center0359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0359 : work0359.theta.ok = true ∧
    work0359.jac.invOK = true ∧ acceptsUnitSq work0359.out = true := by decide +kernel

def cell0359 : CellCertificate where
  tauBall := tau0359
  contactCenter := center0359
  contactBall := contact0359
  work := work0359
  center_sq := center_sq0359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0359.1
  jac_ok := checks0359.2.1
  accepted := checks0359.2.2

def cells : List CellCertificate := [cell0352, cell0353, cell0354, cell0355, cell0356, cell0357, cell0358, cell0359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044

end


