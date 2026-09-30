-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0256
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0256
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:06:00.728165+00:00
-- url     : https://prove2.me/theorems/9ba40820-68e0-421c-a90a-1bbbd271e02e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0256.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2048 : RatBall :=
  ⟨⟨-49/320, 101/320⟩, 3/640⟩
def center2048 : GaussianRat :=
  ⟨-3652061/31250000, 220423219/1000000000⟩
def contact2048 : RatBall := localContactBall tau2048 center2048
def work2048 : RoundedTauEval :=
  evalTau precision tau2048 contact2048 logTwoBall

theorem center_sq2048 : (center2048.re : ℝ)^2 +
    (center2048.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2048]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2048 : work2048.theta.ok = true ∧
    work2048.jac.invOK = true ∧ acceptsUnitSq work2048.out = true := by decide +kernel

def cell2048 : CellCertificate where
  tauBall := tau2048
  contactCenter := center2048
  contactBall := contact2048
  work := work2048
  center_sq := center_sq2048
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2048.1
  jac_ok := checks2048.2.1
  accepted := checks2048.2.2

def tau2049 : RatBall :=
  ⟨⟨-51/320, 103/320⟩, 3/640⟩
def center2049 : GaussianRat :=
  ⟨-7627513/62500000, 224552577/1000000000⟩
def contact2049 : RatBall := localContactBall tau2049 center2049
def work2049 : RoundedTauEval :=
  evalTau precision tau2049 contact2049 logTwoBall

theorem center_sq2049 : (center2049.re : ℝ)^2 +
    (center2049.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2049]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2049 : work2049.theta.ok = true ∧
    work2049.jac.invOK = true ∧ acceptsUnitSq work2049.out = true := by decide +kernel

def cell2049 : CellCertificate where
  tauBall := tau2049
  contactCenter := center2049
  contactBall := contact2049
  work := work2049
  center_sq := center_sq2049
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2049.1
  jac_ok := checks2049.2.1
  accepted := checks2049.2.2

def tau2050 : RatBall :=
  ⟨⟨-49/320, 103/320⟩, 3/640⟩
def center2050 : GaussianRat :=
  ⟨-117379261/1000000000, 56270573/250000000⟩
def contact2050 : RatBall := localContactBall tau2050 center2050
def work2050 : RoundedTauEval :=
  evalTau precision tau2050 contact2050 logTwoBall

theorem center_sq2050 : (center2050.re : ℝ)^2 +
    (center2050.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2050]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2050 : work2050.theta.ok = true ∧
    work2050.jac.invOK = true ∧ acceptsUnitSq work2050.out = true := by decide +kernel

def cell2050 : CellCertificate where
  tauBall := tau2050
  contactCenter := center2050
  contactBall := contact2050
  work := work2050
  center_sq := center_sq2050
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2050.1
  jac_ok := checks2050.2.1
  accepted := checks2050.2.2

def tau2051 : RatBall :=
  ⟨⟨-63/320, 21/64⟩, 3/640⟩
def center2051 : GaussianRat :=
  ⟨-75163641/500000000, 225566837/1000000000⟩
def contact2051 : RatBall := localContactBall tau2051 center2051
def work2051 : RoundedTauEval :=
  evalTau precision tau2051 contact2051 logTwoBall

theorem center_sq2051 : (center2051.re : ℝ)^2 +
    (center2051.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2051]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2051 : work2051.theta.ok = true ∧
    work2051.jac.invOK = true ∧ acceptsUnitSq work2051.out = true := by decide +kernel

def cell2051 : CellCertificate where
  tauBall := tau2051
  contactCenter := center2051
  contactBall := contact2051
  work := work2051
  center_sq := center_sq2051
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2051.1
  jac_ok := checks2051.2.1
  accepted := checks2051.2.2

def tau2052 : RatBall :=
  ⟨⟨-61/320, 21/64⟩, 3/640⟩
def center2052 : GaussianRat :=
  ⟨-145746161/1000000000, 113109273/500000000⟩
def contact2052 : RatBall := localContactBall tau2052 center2052
def work2052 : RoundedTauEval :=
  evalTau precision tau2052 contact2052 logTwoBall

theorem center_sq2052 : (center2052.re : ℝ)^2 +
    (center2052.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2052]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2052 : work2052.theta.ok = true ∧
    work2052.jac.invOK = true ∧ acceptsUnitSq work2052.out = true := by decide +kernel

def cell2052 : CellCertificate where
  tauBall := tau2052
  contactCenter := center2052
  contactBall := contact2052
  work := work2052
  center_sq := center_sq2052
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2052.1
  jac_ok := checks2052.2.1
  accepted := checks2052.2.2

def tau2053 : RatBall :=
  ⟨⟨-63/320, 107/320⟩, 3/640⟩
def center2053 : GaussianRat :=
  ⟨-150996377/1000000000, 230147447/1000000000⟩
def contact2053 : RatBall := localContactBall tau2053 center2053
def work2053 : RoundedTauEval :=
  evalTau precision tau2053 contact2053 logTwoBall

theorem center_sq2053 : (center2053.re : ℝ)^2 +
    (center2053.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2053]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2053 : work2053.theta.ok = true ∧
    work2053.jac.invOK = true ∧ acceptsUnitSq work2053.out = true := by decide +kernel

def cell2053 : CellCertificate where
  tauBall := tau2053
  contactCenter := center2053
  contactBall := contact2053
  work := work2053
  center_sq := center_sq2053
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2053.1
  jac_ok := checks2053.2.1
  accepted := checks2053.2.2

def tau2054 : RatBall :=
  ⟨⟨-61/320, 107/320⟩, 3/640⟩
def center2054 : GaussianRat :=
  ⟨-146398251/1000000000, 115408523/500000000⟩
def contact2054 : RatBall := localContactBall tau2054 center2054
def work2054 : RoundedTauEval :=
  evalTau precision tau2054 contact2054 logTwoBall

theorem center_sq2054 : (center2054.re : ℝ)^2 +
    (center2054.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2054]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2054 : work2054.theta.ok = true ∧
    work2054.jac.invOK = true ∧ acceptsUnitSq work2054.out = true := by decide +kernel

def cell2054 : CellCertificate where
  tauBall := tau2054
  contactCenter := center2054
  contactBall := contact2054
  work := work2054
  center_sq := center_sq2054
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2054.1
  jac_ok := checks2054.2.1
  accepted := checks2054.2.2

def tau2055 : RatBall :=
  ⟨⟨-59/320, 21/64⟩, 3/640⟩
def center2055 : GaussianRat :=
  ⟨-70573769/500000000, 113426637/500000000⟩
def contact2055 : RatBall := localContactBall tau2055 center2055
def work2055 : RoundedTauEval :=
  evalTau precision tau2055 contact2055 logTwoBall

theorem center_sq2055 : (center2055.re : ℝ)^2 +
    (center2055.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2055]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2055 : work2055.theta.ok = true ∧
    work2055.jac.invOK = true ∧ acceptsUnitSq work2055.out = true := by decide +kernel

def cell2055 : CellCertificate where
  tauBall := tau2055
  contactCenter := center2055
  contactBall := contact2055
  work := work2055
  center_sq := center_sq2055
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2055.1
  jac_ok := checks2055.2.1
  accepted := checks2055.2.2

def cells : List CellCertificate := [cell2048, cell2049, cell2050, cell2051, cell2052, cell2053, cell2054, cell2055]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256

end


