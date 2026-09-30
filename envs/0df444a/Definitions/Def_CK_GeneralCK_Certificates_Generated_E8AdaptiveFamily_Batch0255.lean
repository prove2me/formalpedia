-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0255
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0255
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:49:15.05345+00:00
-- url     : https://prove2.me/theorems/72da9533-db7d-43eb-9166-ee5cffc83997
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0255.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2040 : RatBall :=
  ⟨⟨-57/320, 101/320⟩, 3/640⟩
def center2040 : GaussianRat :=
  ⟨-135347471/1000000000, 43651451/200000000⟩
def contact2040 : RatBall := localContactBall tau2040 center2040
def work2040 : RoundedTauEval :=
  evalTau precision tau2040 contact2040 logTwoBall

theorem center_sq2040 : (center2040.re : ℝ)^2 +
    (center2040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2040 : work2040.theta.ok = true ∧
    work2040.jac.invOK = true ∧ acceptsUnitSq work2040.out = true := by decide +kernel

def cell2040 : CellCertificate where
  tauBall := tau2040
  contactCenter := center2040
  contactBall := contact2040
  work := work2040
  center_sq := center_sq2040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2040.1
  jac_ok := checks2040.2.1
  accepted := checks2040.2.2

def tau2041 : RatBall :=
  ⟨⟨-59/320, 103/320⟩, 3/640⟩
def center2041 : GaussianRat :=
  ⟨-140529903/1000000000, 222254637/1000000000⟩
def contact2041 : RatBall := localContactBall tau2041 center2041
def work2041 : RoundedTauEval :=
  evalTau precision tau2041 contact2041 logTwoBall

theorem center_sq2041 : (center2041.re : ℝ)^2 +
    (center2041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2041 : work2041.theta.ok = true ∧
    work2041.jac.invOK = true ∧ acceptsUnitSq work2041.out = true := by decide +kernel

def cell2041 : CellCertificate where
  tauBall := tau2041
  contactCenter := center2041
  contactBall := contact2041
  work := work2041
  center_sq := center_sq2041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2041.1
  jac_ok := checks2041.2.1
  accepted := checks2041.2.2

def tau2042 : RatBall :=
  ⟨⟨-57/320, 103/320⟩, 3/640⟩
def center2042 : GaussianRat :=
  ⟨-135931497/1000000000, 55713833/250000000⟩
def contact2042 : RatBall := localContactBall tau2042 center2042
def work2042 : RoundedTauEval :=
  evalTau precision tau2042 contact2042 logTwoBall

theorem center_sq2042 : (center2042.re : ℝ)^2 +
    (center2042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2042 : work2042.theta.ok = true ∧
    work2042.jac.invOK = true ∧ acceptsUnitSq work2042.out = true := by decide +kernel

def cell2042 : CellCertificate where
  tauBall := tau2042
  contactCenter := center2042
  contactBall := contact2042
  work := work2042
  center_sq := center_sq2042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2042.1
  jac_ok := checks2042.2.1
  accepted := checks2042.2.2

def tau2043 : RatBall :=
  ⟨⟨-11/64, 101/320⟩, 3/640⟩
def center2043 : GaussianRat :=
  ⟨-3268749/25000000, 54706193/250000000⟩
def contact2043 : RatBall := localContactBall tau2043 center2043
def work2043 : RoundedTauEval :=
  evalTau precision tau2043 contact2043 logTwoBall

theorem center_sq2043 : (center2043.re : ℝ)^2 +
    (center2043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2043 : work2043.theta.ok = true ∧
    work2043.jac.invOK = true ∧ acceptsUnitSq work2043.out = true := by decide +kernel

def cell2043 : CellCertificate where
  tauBall := tau2043
  contactCenter := center2043
  contactBall := contact2043
  work := work2043
  center_sq := center_sq2043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2043.1
  jac_ok := checks2043.2.1
  accepted := checks2043.2.2

def tau2044 : RatBall :=
  ⟨⟨-53/320, 101/320⟩, 3/640⟩
def center2044 : GaussianRat :=
  ⟨-15767113/125000000, 219375147/1000000000⟩
def contact2044 : RatBall := localContactBall tau2044 center2044
def work2044 : RoundedTauEval :=
  evalTau precision tau2044 contact2044 logTwoBall

theorem center_sq2044 : (center2044.re : ℝ)^2 +
    (center2044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2044 : work2044.theta.ok = true ∧
    work2044.jac.invOK = true ∧ acceptsUnitSq work2044.out = true := by decide +kernel

def cell2044 : CellCertificate where
  tauBall := tau2044
  contactCenter := center2044
  contactBall := contact2044
  work := work2044
  center_sq := center_sq2044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2044.1
  jac_ok := checks2044.2.1
  accepted := checks2044.2.2

def tau2045 : RatBall :=
  ⟨⟨-11/64, 103/320⟩, 3/640⟩
def center2045 : GaussianRat :=
  ⟨-8207299/62500000, 8937551/40000000⟩
def contact2045 : RatBall := localContactBall tau2045 center2045
def work2045 : RoundedTauEval :=
  evalTau precision tau2045 contact2045 logTwoBall

theorem center_sq2045 : (center2045.re : ℝ)^2 +
    (center2045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2045 : work2045.theta.ok = true ∧
    work2045.jac.invOK = true ∧ acceptsUnitSq work2045.out = true := by decide +kernel

def cell2045 : CellCertificate where
  tauBall := tau2045
  contactCenter := center2045
  contactBall := contact2045
  work := work2045
  center_sq := center_sq2045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2045.1
  jac_ok := checks2045.2.1
  accepted := checks2045.2.2

def tau2046 : RatBall :=
  ⟨⟨-53/320, 103/320⟩, 3/640⟩
def center2046 : GaussianRat :=
  ⟨-126686203/1000000000, 224004631/1000000000⟩
def contact2046 : RatBall := localContactBall tau2046 center2046
def work2046 : RoundedTauEval :=
  evalTau precision tau2046 contact2046 logTwoBall

theorem center_sq2046 : (center2046.re : ℝ)^2 +
    (center2046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2046 : work2046.theta.ok = true ∧
    work2046.jac.invOK = true ∧ acceptsUnitSq work2046.out = true := by decide +kernel

def cell2046 : CellCertificate where
  tauBall := tau2046
  contactCenter := center2046
  contactBall := contact2046
  work := work2046
  center_sq := center_sq2046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2046.1
  jac_ok := checks2046.2.1
  accepted := checks2046.2.2

def tau2047 : RatBall :=
  ⟨⟨-51/320, 101/320⟩, 3/640⟩
def center2047 : GaussianRat :=
  ⟨-30377187/250000000, 6872127/31250000⟩
def contact2047 : RatBall := localContactBall tau2047 center2047
def work2047 : RoundedTauEval :=
  evalTau precision tau2047 contact2047 logTwoBall

theorem center_sq2047 : (center2047.re : ℝ)^2 +
    (center2047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2047 : work2047.theta.ok = true ∧
    work2047.jac.invOK = true ∧ acceptsUnitSq work2047.out = true := by decide +kernel

def cell2047 : CellCertificate where
  tauBall := tau2047
  contactCenter := center2047
  contactBall := contact2047
  work := work2047
  center_sq := center_sq2047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2047.1
  jac_ok := checks2047.2.1
  accepted := checks2047.2.2

def cells : List CellCertificate := [cell2040, cell2041, cell2042, cell2043, cell2044, cell2045, cell2046, cell2047]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255

end


