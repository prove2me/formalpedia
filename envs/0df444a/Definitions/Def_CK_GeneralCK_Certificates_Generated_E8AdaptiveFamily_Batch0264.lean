-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0264
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0264
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:05:10.591026+00:00
-- url     : https://prove2.me/theorems/617b6020-4b89-445e-988c-3633fd499066
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0264.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2112 : RatBall :=
  ⟨⟨-33/320, 111/320⟩, 3/640⟩
def center2112 : GaussianRat :=
  ⟨-20287513/250000000, 247870587/1000000000⟩
def contact2112 : RatBall := localContactBall tau2112 center2112
def work2112 : RoundedTauEval :=
  evalTau precision tau2112 contact2112 logTwoBall

theorem center_sq2112 : (center2112.re : ℝ)^2 +
    (center2112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2112 : work2112.theta.ok = true ∧
    work2112.jac.invOK = true ∧ acceptsUnitSq work2112.out = true := by decide +kernel

def cell2112 : CellCertificate where
  tauBall := tau2112
  contactCenter := center2112
  contactBall := contact2112
  work := work2112
  center_sq := center_sq2112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2112.1
  jac_ok := checks2112.2.1
  accepted := checks2112.2.2

def tau2113 : RatBall :=
  ⟨⟨-53/320, 113/320⟩, 3/640⟩
def center2113 : GaussianRat :=
  ⟨-129670733/1000000000, 15464381/62500000⟩
def contact2113 : RatBall := localContactBall tau2113 center2113
def work2113 : RoundedTauEval :=
  evalTau precision tau2113 contact2113 logTwoBall

theorem center_sq2113 : (center2113.re : ℝ)^2 +
    (center2113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2113 : work2113.theta.ok = true ∧
    work2113.jac.invOK = true ∧ acceptsUnitSq work2113.out = true := by decide +kernel

def cell2113 : CellCertificate where
  tauBall := tau2113
  contactCenter := center2113
  contactBall := contact2113
  work := work2113
  center_sq := center_sq2113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2113.1
  jac_ok := checks2113.2.1
  accepted := checks2113.2.2

def tau2114 : RatBall :=
  ⟨⟨-51/320, 113/320⟩, 3/640⟩
def center2114 : GaussianRat :=
  ⟨-124928411/1000000000, 12402911/50000000⟩
def contact2114 : RatBall := localContactBall tau2114 center2114
def work2114 : RoundedTauEval :=
  evalTau precision tau2114 contact2114 logTwoBall

theorem center_sq2114 : (center2114.re : ℝ)^2 +
    (center2114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2114 : work2114.theta.ok = true ∧
    work2114.jac.invOK = true ∧ acceptsUnitSq work2114.out = true := by decide +kernel

def cell2114 : CellCertificate where
  tauBall := tau2114
  contactCenter := center2114
  contactBall := contact2114
  work := work2114
  center_sq := center_sq2114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2114.1
  jac_ok := checks2114.2.1
  accepted := checks2114.2.2

def tau2115 : RatBall :=
  ⟨⟨-49/320, 113/320⟩, 3/640⟩
def center2115 : GaussianRat :=
  ⟨-120169401/1000000000, 248665661/1000000000⟩
def contact2115 : RatBall := localContactBall tau2115 center2115
def work2115 : RoundedTauEval :=
  evalTau precision tau2115 contact2115 logTwoBall

theorem center_sq2115 : (center2115.re : ℝ)^2 +
    (center2115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2115]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2115 : work2115.theta.ok = true ∧
    work2115.jac.invOK = true ∧ acceptsUnitSq work2115.out = true := by decide +kernel

def cell2115 : CellCertificate where
  tauBall := tau2115
  contactCenter := center2115
  contactBall := contact2115
  work := work2115
  center_sq := center_sq2115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2115.1
  jac_ok := checks2115.2.1
  accepted := checks2115.2.2

def tau2116 : RatBall :=
  ⟨⟨-47/320, 113/320⟩, 3/640⟩
def center2116 : GaussianRat :=
  ⟨-115394221/1000000000, 124626021/500000000⟩
def contact2116 : RatBall := localContactBall tau2116 center2116
def work2116 : RoundedTauEval :=
  evalTau precision tau2116 contact2116 logTwoBall

theorem center_sq2116 : (center2116.re : ℝ)^2 +
    (center2116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2116 : work2116.theta.ok = true ∧
    work2116.jac.invOK = true ∧ acceptsUnitSq work2116.out = true := by decide +kernel

def cell2116 : CellCertificate where
  tauBall := tau2116
  contactCenter := center2116
  contactBall := contact2116
  work := work2116
  center_sq := center_sq2116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2116.1
  jac_ok := checks2116.2.1
  accepted := checks2116.2.2

def tau2117 : RatBall :=
  ⟨⟨-9/64, 113/320⟩, 3/640⟩
def center2117 : GaussianRat :=
  ⟨-22120681/200000000, 249816993/1000000000⟩
def contact2117 : RatBall := localContactBall tau2117 center2117
def work2117 : RoundedTauEval :=
  evalTau precision tau2117 contact2117 logTwoBall

theorem center_sq2117 : (center2117.re : ℝ)^2 +
    (center2117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2117 : work2117.theta.ok = true ∧
    work2117.jac.invOK = true ∧ acceptsUnitSq work2117.out = true := by decide +kernel

def cell2117 : CellCertificate where
  tauBall := tau2117
  contactCenter := center2117
  contactBall := contact2117
  work := work2117
  center_sq := center_sq2117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2117.1
  jac_ok := checks2117.2.1
  accepted := checks2117.2.2

def tau2118 : RatBall :=
  ⟨⟨-9/64, 23/64⟩, 3/640⟩
def center2118 : GaussianRat :=
  ⟨-889321/8000000, 254626433/1000000000⟩
def contact2118 : RatBall := localContactBall tau2118 center2118
def work2118 : RoundedTauEval :=
  evalTau precision tau2118 contact2118 logTwoBall

theorem center_sq2118 : (center2118.re : ℝ)^2 +
    (center2118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2118 : work2118.theta.ok = true ∧
    work2118.jac.invOK = true ∧ acceptsUnitSq work2118.out = true := by decide +kernel

def cell2118 : CellCertificate where
  tauBall := tau2118
  contactCenter := center2118
  contactBall := contact2118
  work := work2118
  center_sq := center_sq2118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2118.1
  jac_ok := checks2118.2.1
  accepted := checks2118.2.2

def tau2119 : RatBall :=
  ⟨⟨-43/320, 113/320⟩, 3/640⟩
def center2119 : GaussianRat :=
  ⟨-105797499/1000000000, 62590039/250000000⟩
def contact2119 : RatBall := localContactBall tau2119 center2119
def work2119 : RoundedTauEval :=
  evalTau precision tau2119 contact2119 logTwoBall

theorem center_sq2119 : (center2119.re : ℝ)^2 +
    (center2119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2119]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2119 : work2119.theta.ok = true ∧
    work2119.jac.invOK = true ∧ acceptsUnitSq work2119.out = true := by decide +kernel

def cell2119 : CellCertificate where
  tauBall := tau2119
  contactCenter := center2119
  contactBall := contact2119
  work := work2119
  center_sq := center_sq2119
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2119.1
  jac_ok := checks2119.2.1
  accepted := checks2119.2.2

def cells : List CellCertificate := [cell2112, cell2113, cell2114, cell2115, cell2116, cell2117, cell2118, cell2119]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264

end


