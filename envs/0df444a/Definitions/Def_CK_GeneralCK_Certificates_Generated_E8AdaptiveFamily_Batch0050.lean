-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0050
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0050
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:03:50.43039+00:00
-- url     : https://prove2.me/theorems/ac3b0476-589c-4e0a-b8ce-8bd71f1a1c58
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0050.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0400 : RatBall :=
  ⟨⟨-17/160, -51/160⟩, 3/320⟩
def center0400 : GaussianRat :=
  ⟨-40905123/500000000, -113032697/500000000⟩
def contact0400 : RatBall := localContactBall tau0400 center0400
def work0400 : RoundedTauEval :=
  evalTau precision tau0400 contact0400 logTwoBall

theorem center_sq0400 : (center0400.re : ℝ)^2 +
    (center0400.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0400]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0400 : work0400.theta.ok = true ∧
    work0400.jac.invOK = true ∧ acceptsUnitSq work0400.out = true := by decide +kernel

def cell0400 : CellCertificate where
  tauBall := tau0400
  contactCenter := center0400
  contactBall := contact0400
  work := work0400
  center_sq := center_sq0400
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0400.1
  jac_ok := checks0400.2.1
  accepted := checks0400.2.2

def tau0401 : RatBall :=
  ⟨⟨-19/160, -49/160⟩, 3/320⟩
def center0401 : GaussianRat :=
  ⟨-90499187/1000000000, -215867147/1000000000⟩
def contact0401 : RatBall := localContactBall tau0401 center0401
def work0401 : RoundedTauEval :=
  evalTau precision tau0401 contact0401 logTwoBall

theorem center_sq0401 : (center0401.re : ℝ)^2 +
    (center0401.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0401]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0401 : work0401.theta.ok = true ∧
    work0401.jac.invOK = true ∧ acceptsUnitSq work0401.out = true := by decide +kernel

def cell0401 : CellCertificate where
  tauBall := tau0401
  contactCenter := center0401
  contactBall := contact0401
  work := work0401
  center_sq := center_sq0401
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0401.1
  jac_ok := checks0401.2.1
  accepted := checks0401.2.2

def tau0402 : RatBall :=
  ⟨⟨-17/160, -49/160⟩, 3/320⟩
def center0402 : GaussianRat :=
  ⟨-5068403/62500000, -846097/3906250⟩
def contact0402 : RatBall := localContactBall tau0402 center0402
def work0402 : RoundedTauEval :=
  evalTau precision tau0402 contact0402 logTwoBall

theorem center_sq0402 : (center0402.re : ℝ)^2 +
    (center0402.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0402]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0402 : work0402.theta.ok = true ∧
    work0402.jac.invOK = true ∧ acceptsUnitSq work0402.out = true := by decide +kernel

def cell0402 : CellCertificate where
  tauBall := tau0402
  contactCenter := center0402
  contactBall := contact0402
  work := work0402
  center_sq := center_sq0402
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0402.1
  jac_ok := checks0402.2.1
  accepted := checks0402.2.2

def tau0403 : RatBall :=
  ⟨⟨-1/160, -57/160⟩, 3/320⟩
def center0403 : GaussianRat :=
  ⟨-311809/62500000, -5174291/20000000⟩
def contact0403 : RatBall := localContactBall tau0403 center0403
def work0403 : RoundedTauEval :=
  evalTau precision tau0403 contact0403 logTwoBall

theorem center_sq0403 : (center0403.re : ℝ)^2 +
    (center0403.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0403]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0403 : work0403.theta.ok = true ∧
    work0403.jac.invOK = true ∧ acceptsUnitSq work0403.out = true := by decide +kernel

def cell0403 : CellCertificate where
  tauBall := tau0403
  contactCenter := center0403
  contactBall := contact0403
  work := work0403
  center_sq := center_sq0403
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0403.1
  jac_ok := checks0403.2.1
  accepted := checks0403.2.2

def tau0404 : RatBall :=
  ⟨⟨-3/32, -53/160⟩, 3/320⟩
def center0404 : GaussianRat :=
  ⟨-72958787/1000000000, -47269393/200000000⟩
def contact0404 : RatBall := localContactBall tau0404 center0404
def work0404 : RoundedTauEval :=
  evalTau precision tau0404 contact0404 logTwoBall

theorem center_sq0404 : (center0404.re : ℝ)^2 +
    (center0404.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0404]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0404 : work0404.theta.ok = true ∧
    work0404.jac.invOK = true ∧ acceptsUnitSq work0404.out = true := by decide +kernel

def cell0404 : CellCertificate where
  tauBall := tau0404
  contactCenter := center0404
  contactBall := contact0404
  work := work0404
  center_sq := center_sq0404
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0404.1
  jac_ok := checks0404.2.1
  accepted := checks0404.2.2

def tau0405 : RatBall :=
  ⟨⟨-13/160, -53/160⟩, 3/320⟩
def center0405 : GaussianRat :=
  ⟨-63310961/1000000000, -236995059/1000000000⟩
def contact0405 : RatBall := localContactBall tau0405 center0405
def work0405 : RoundedTauEval :=
  evalTau precision tau0405 contact0405 logTwoBall

theorem center_sq0405 : (center0405.re : ℝ)^2 +
    (center0405.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0405]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0405 : work0405.theta.ok = true ∧
    work0405.jac.invOK = true ∧ acceptsUnitSq work0405.out = true := by decide +kernel

def cell0405 : CellCertificate where
  tauBall := tau0405
  contactCenter := center0405
  contactBall := contact0405
  work := work0405
  center_sq := center_sq0405
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0405.1
  jac_ok := checks0405.2.1
  accepted := checks0405.2.2

def tau0406 : RatBall :=
  ⟨⟨-9/160, -11/32⟩, 3/320⟩
def center0406 : GaussianRat :=
  ⟨-44352537/1000000000, -61948059/250000000⟩
def contact0406 : RatBall := localContactBall tau0406 center0406
def work0406 : RoundedTauEval :=
  evalTau precision tau0406 contact0406 logTwoBall

theorem center_sq0406 : (center0406.re : ℝ)^2 +
    (center0406.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0406]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0406 : work0406.theta.ok = true ∧
    work0406.jac.invOK = true ∧ acceptsUnitSq work0406.out = true := by decide +kernel

def cell0406 : CellCertificate where
  tauBall := tau0406
  contactCenter := center0406
  contactBall := contact0406
  work := work0406
  center_sq := center_sq0406
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0406.1
  jac_ok := checks0406.2.1
  accepted := checks0406.2.2

def tau0407 : RatBall :=
  ⟨⟨-11/160, -53/160⟩, 3/320⟩
def center0407 : GaussianRat :=
  ⟨-53629143/1000000000, -118776899/500000000⟩
def contact0407 : RatBall := localContactBall tau0407 center0407
def work0407 : RoundedTauEval :=
  evalTau precision tau0407 contact0407 logTwoBall

theorem center_sq0407 : (center0407.re : ℝ)^2 +
    (center0407.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0407]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0407 : work0407.theta.ok = true ∧
    work0407.jac.invOK = true ∧ acceptsUnitSq work0407.out = true := by decide +kernel

def cell0407 : CellCertificate where
  tauBall := tau0407
  contactCenter := center0407
  contactBall := contact0407
  work := work0407
  center_sq := center_sq0407
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0407.1
  jac_ok := checks0407.2.1
  accepted := checks0407.2.2

def cells : List CellCertificate := [cell0400, cell0401, cell0402, cell0403, cell0404, cell0405, cell0406, cell0407]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050

end


