-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0062
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0062
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:39:50.556752+00:00
-- url     : https://prove2.me/theorems/a9bf116d-aab4-4053-a188-14c44e1979f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0062.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0496 : RatBall :=
  ⟨⟨-11/32, -5/32⟩, 3/320⟩
def center0496 : GaussianRat :=
  ⟨-234063587/1000000000, -96845571/1000000000⟩
def contact0496 : RatBall := localContactBall tau0496 center0496
def work0496 : RoundedTauEval :=
  evalTau precision tau0496 contact0496 logTwoBall

theorem center_sq0496 : (center0496.re : ℝ)^2 +
    (center0496.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0496]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0496 : work0496.theta.ok = true ∧
    work0496.jac.invOK = true ∧ acceptsUnitSq work0496.out = true := by decide +kernel

def cell0496 : CellCertificate where
  tauBall := tau0496
  contactCenter := center0496
  contactBall := contact0496
  work := work0496
  center_sq := center_sq0496
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0496.1
  jac_ok := checks0496.2.1
  accepted := checks0496.2.2

def tau0497 : RatBall :=
  ⟨⟨-53/160, -5/32⟩, 3/320⟩
def center0497 : GaussianRat :=
  ⟨-226215887/1000000000, -24408867/250000000⟩
def contact0497 : RatBall := localContactBall tau0497 center0497
def work0497 : RoundedTauEval :=
  evalTau precision tau0497 contact0497 logTwoBall

theorem center_sq0497 : (center0497.re : ℝ)^2 +
    (center0497.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0497]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0497 : work0497.theta.ok = true ∧
    work0497.jac.invOK = true ∧ acceptsUnitSq work0497.out = true := by decide +kernel

def cell0497 : CellCertificate where
  tauBall := tau0497
  contactCenter := center0497
  contactBall := contact0497
  work := work0497
  center_sq := center_sq0497
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0497.1
  jac_ok := checks0497.2.1
  accepted := checks0497.2.2

def tau0498 : RatBall :=
  ⟨⟨-51/160, -27/160⟩, 3/320⟩
def center0498 : GaussianRat :=
  ⟨-219098349/1000000000, -53182749/500000000⟩
def contact0498 : RatBall := localContactBall tau0498 center0498
def work0498 : RoundedTauEval :=
  evalTau precision tau0498 contact0498 logTwoBall

theorem center_sq0498 : (center0498.re : ℝ)^2 +
    (center0498.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0498]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0498 : work0498.theta.ok = true ∧
    work0498.jac.invOK = true ∧ acceptsUnitSq work0498.out = true := by decide +kernel

def cell0498 : CellCertificate where
  tauBall := tau0498
  contactCenter := center0498
  contactBall := contact0498
  work := work0498
  center_sq := center_sq0498
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0498.1
  jac_ok := checks0498.2.1
  accepted := checks0498.2.2

def tau0499 : RatBall :=
  ⟨⟨-49/160, -27/160⟩, 3/320⟩
def center0499 : GaussianRat :=
  ⟨-211098659/1000000000, -10718597/100000000⟩
def contact0499 : RatBall := localContactBall tau0499 center0499
def work0499 : RoundedTauEval :=
  evalTau precision tau0499 contact0499 logTwoBall

theorem center_sq0499 : (center0499.re : ℝ)^2 +
    (center0499.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0499]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0499 : work0499.theta.ok = true ∧
    work0499.jac.invOK = true ∧ acceptsUnitSq work0499.out = true := by decide +kernel

def cell0499 : CellCertificate where
  tauBall := tau0499
  contactCenter := center0499
  contactBall := contact0499
  work := work0499
  center_sq := center_sq0499
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0499.1
  jac_ok := checks0499.2.1
  accepted := checks0499.2.2

def tau0500 : RatBall :=
  ⟨⟨-51/160, -5/32⟩, 3/320⟩
def center0500 : GaussianRat :=
  ⟨-5457529/25000000, -49204231/500000000⟩
def contact0500 : RatBall := localContactBall tau0500 center0500
def work0500 : RoundedTauEval :=
  evalTau precision tau0500 contact0500 logTwoBall

theorem center_sq0500 : (center0500.re : ℝ)^2 +
    (center0500.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0500]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0500 : work0500.theta.ok = true ∧
    work0500.jac.invOK = true ∧ acceptsUnitSq work0500.out = true := by decide +kernel

def cell0500 : CellCertificate where
  tauBall := tau0500
  contactCenter := center0500
  contactBall := contact0500
  work := work0500
  center_sq := center_sq0500
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0500.1
  jac_ok := checks0500.2.1
  accepted := checks0500.2.2

def tau0501 : RatBall :=
  ⟨⟨-49/160, -5/32⟩, 3/320⟩
def center0501 : GaussianRat :=
  ⟨-52580197/250000000, -1239543/12500000⟩
def contact0501 : RatBall := localContactBall tau0501 center0501
def work0501 : RoundedTauEval :=
  evalTau precision tau0501 contact0501 logTwoBall

theorem center_sq0501 : (center0501.re : ℝ)^2 +
    (center0501.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0501]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0501 : work0501.theta.ok = true ∧
    work0501.jac.invOK = true ∧ acceptsUnitSq work0501.out = true := by decide +kernel

def cell0501 : CellCertificate where
  tauBall := tau0501
  contactCenter := center0501
  contactBall := contact0501
  work := work0501
  center_sq := center_sq0501
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0501.1
  jac_ok := checks0501.2.1
  accepted := checks0501.2.2

def tau0502 : RatBall :=
  ⟨⟨-61/160, -23/160⟩, 3/320⟩
def center0502 : GaussianRat :=
  ⟨-64096843/250000000, -86787913/1000000000⟩
def contact0502 : RatBall := localContactBall tau0502 center0502
def work0502 : RoundedTauEval :=
  evalTau precision tau0502 contact0502 logTwoBall

theorem center_sq0502 : (center0502.re : ℝ)^2 +
    (center0502.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0502]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0502 : work0502.theta.ok = true ∧
    work0502.jac.invOK = true ∧ acceptsUnitSq work0502.out = true := by decide +kernel

def cell0502 : CellCertificate where
  tauBall := tau0502
  contactCenter := center0502
  contactBall := contact0502
  work := work0502
  center_sq := center_sq0502
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0502.1
  jac_ok := checks0502.2.1
  accepted := checks0502.2.2

def tau0503 : RatBall :=
  ⟨⟨-61/160, -21/160⟩, 3/320⟩
def center0503 : GaussianRat :=
  ⟨-15978319/62500000, -79201909/1000000000⟩
def contact0503 : RatBall := localContactBall tau0503 center0503
def work0503 : RoundedTauEval :=
  evalTau precision tau0503 contact0503 logTwoBall

theorem center_sq0503 : (center0503.re : ℝ)^2 +
    (center0503.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0503]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0503 : work0503.theta.ok = true ∧
    work0503.jac.invOK = true ∧ acceptsUnitSq work0503.out = true := by decide +kernel

def cell0503 : CellCertificate where
  tauBall := tau0503
  contactCenter := center0503
  contactBall := contact0503
  work := work0503
  center_sq := center_sq0503
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0503.1
  jac_ok := checks0503.2.1
  accepted := checks0503.2.2

def cells : List CellCertificate := [cell0496, cell0497, cell0498, cell0499, cell0500, cell0501, cell0502, cell0503]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062

end


