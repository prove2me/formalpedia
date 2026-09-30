-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0010
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0010
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:53:59.099727+00:00
-- url     : https://prove2.me/theorems/7dda7eef-b4ad-49f6-9565-9c4c2f64516b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0010.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0080 : RatBall :=
  ⟨⟨-21/80, -9/80⟩, 3/160⟩
def center0080 : GaussianRat :=
  ⟨-44973153/250000000, -72980409/1000000000⟩
def contact0080 : RatBall := localContactBall tau0080 center0080
def work0080 : RoundedTauEval :=
  evalTau precision tau0080 contact0080 logTwoBall

theorem center_sq0080 : (center0080.re : ℝ)^2 +
    (center0080.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0080]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0080 : work0080.theta.ok = true ∧
    work0080.jac.invOK = true ∧ acceptsUnitSq work0080.out = true := by decide +kernel

def cell0080 : CellCertificate where
  tauBall := tau0080
  contactCenter := center0080
  contactBall := contact0080
  work := work0080
  center_sq := center_sq0080
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0080.1
  jac_ok := checks0080.2.1
  accepted := checks0080.2.2

def tau0081 : RatBall :=
  ⟨⟨-19/80, -11/80⟩, 3/160⟩
def center0081 : GaussianRat :=
  ⟨-82225973/500000000, -18092371/200000000⟩
def contact0081 : RatBall := localContactBall tau0081 center0081
def work0081 : RoundedTauEval :=
  evalTau precision tau0081 contact0081 logTwoBall

theorem center_sq0081 : (center0081.re : ℝ)^2 +
    (center0081.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0081]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0081 : work0081.theta.ok = true ∧
    work0081.jac.invOK = true ∧ acceptsUnitSq work0081.out = true := by decide +kernel

def cell0081 : CellCertificate where
  tauBall := tau0081
  contactCenter := center0081
  contactBall := contact0081
  work := work0081
  center_sq := center_sq0081
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0081.1
  jac_ok := checks0081.2.1
  accepted := checks0081.2.2

def tau0082 : RatBall :=
  ⟨⟨-17/80, -11/80⟩, 3/160⟩
def center0082 : GaussianRat :=
  ⟨-1154229/7812500, -91503559/1000000000⟩
def contact0082 : RatBall := localContactBall tau0082 center0082
def work0082 : RoundedTauEval :=
  evalTau precision tau0082 contact0082 logTwoBall

theorem center_sq0082 : (center0082.re : ℝ)^2 +
    (center0082.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0082]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0082 : work0082.theta.ok = true ∧
    work0082.jac.invOK = true ∧ acceptsUnitSq work0082.out = true := by decide +kernel

def cell0082 : CellCertificate where
  tauBall := tau0082
  contactCenter := center0082
  contactBall := contact0082
  work := work0082
  center_sq := center_sq0082
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0082.1
  jac_ok := checks0082.2.1
  accepted := checks0082.2.2

def tau0083 : RatBall :=
  ⟨⟨-19/80, -9/80⟩, 3/160⟩
def center0083 : GaussianRat :=
  ⟨-163469111/1000000000, -36947527/500000000⟩
def contact0083 : RatBall := localContactBall tau0083 center0083
def work0083 : RoundedTauEval :=
  evalTau precision tau0083 contact0083 logTwoBall

theorem center_sq0083 : (center0083.re : ℝ)^2 +
    (center0083.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0083]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0083 : work0083.theta.ok = true ∧
    work0083.jac.invOK = true ∧ acceptsUnitSq work0083.out = true := by decide +kernel

def cell0083 : CellCertificate where
  tauBall := tau0083
  contactCenter := center0083
  contactBall := contact0083
  work := work0083
  center_sq := center_sq0083
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0083.1
  jac_ok := checks0083.2.1
  accepted := checks0083.2.2

def tau0084 : RatBall :=
  ⟨⟨-17/80, -9/80⟩, 3/160⟩
def center0084 : GaussianRat :=
  ⟨-29368329/200000000, -18684497/250000000⟩
def contact0084 : RatBall := localContactBall tau0084 center0084
def work0084 : RoundedTauEval :=
  evalTau precision tau0084 contact0084 logTwoBall

theorem center_sq0084 : (center0084.re : ℝ)^2 +
    (center0084.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0084]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0084 : work0084.theta.ok = true ∧
    work0084.jac.invOK = true ∧ acceptsUnitSq work0084.out = true := by decide +kernel

def cell0084 : CellCertificate where
  tauBall := tau0084
  contactCenter := center0084
  contactBall := contact0084
  work := work0084
  center_sq := center_sq0084
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0084.1
  jac_ok := checks0084.2.1
  accepted := checks0084.2.2

def tau0085 : RatBall :=
  ⟨⟨-29/80, -1/16⟩, 3/160⟩
def center0085 : GaussianRat :=
  ⟨-241459683/1000000000, -9531797/250000000⟩
def contact0085 : RatBall := localContactBall tau0085 center0085
def work0085 : RoundedTauEval :=
  evalTau precision tau0085 contact0085 logTwoBall

theorem center_sq0085 : (center0085.re : ℝ)^2 +
    (center0085.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0085]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0085 : work0085.theta.ok = true ∧
    work0085.jac.invOK = true ∧ acceptsUnitSq work0085.out = true := by decide +kernel

def cell0085 : CellCertificate where
  tauBall := tau0085
  contactCenter := center0085
  contactBall := contact0085
  work := work0085
  center_sq := center_sq0085
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0085.1
  jac_ok := checks0085.2.1
  accepted := checks0085.2.2

def tau0086 : RatBall :=
  ⟨⟨-27/80, -7/80⟩, 3/160⟩
def center0086 : GaussianRat :=
  ⟨-14175019/62500000, -54291363/1000000000⟩
def contact0086 : RatBall := localContactBall tau0086 center0086
def work0086 : RoundedTauEval :=
  evalTau precision tau0086 contact0086 logTwoBall

theorem center_sq0086 : (center0086.re : ℝ)^2 +
    (center0086.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0086]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0086 : work0086.theta.ok = true ∧
    work0086.jac.invOK = true ∧ acceptsUnitSq work0086.out = true := by decide +kernel

def cell0086 : CellCertificate where
  tauBall := tau0086
  contactCenter := center0086
  contactBall := contact0086
  work := work0086
  center_sq := center_sq0086
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0086.1
  jac_ok := checks0086.2.1
  accepted := checks0086.2.2

def tau0087 : RatBall :=
  ⟨⟨-5/16, -7/80⟩, 3/160⟩
def center0087 : GaussianRat :=
  ⟨-211121197/1000000000, -55135609/1000000000⟩
def contact0087 : RatBall := localContactBall tau0087 center0087
def work0087 : RoundedTauEval :=
  evalTau precision tau0087 contact0087 logTwoBall

theorem center_sq0087 : (center0087.re : ℝ)^2 +
    (center0087.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0087]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0087 : work0087.theta.ok = true ∧
    work0087.jac.invOK = true ∧ acceptsUnitSq work0087.out = true := by decide +kernel

def cell0087 : CellCertificate where
  tauBall := tau0087
  contactCenter := center0087
  contactBall := contact0087
  work := work0087
  center_sq := center_sq0087
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0087.1
  jac_ok := checks0087.2.1
  accepted := checks0087.2.2

def cells : List CellCertificate := [cell0080, cell0081, cell0082, cell0083, cell0084, cell0085, cell0086, cell0087]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010

end


