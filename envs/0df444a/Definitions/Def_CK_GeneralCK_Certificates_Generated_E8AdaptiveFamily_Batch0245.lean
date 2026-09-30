-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0245
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0245
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:20:31.05735+00:00
-- url     : https://prove2.me/theorems/c184aa24-7280-4b08-a2c1-7e9a89bd7898
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0245.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1960 : RatBall :=
  ⟨⟨-77/320, 89/320⟩, 3/640⟩
def center1960 : GaussianRat :=
  ⟨-88177939/500000000, 185479027/1000000000⟩
def contact1960 : RatBall := localContactBall tau1960 center1960
def work1960 : RoundedTauEval :=
  evalTau precision tau1960 contact1960 logTwoBall

theorem center_sq1960 : (center1960.re : ℝ)^2 +
    (center1960.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1960]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1960 : work1960.theta.ok = true ∧
    work1960.jac.invOK = true ∧ acceptsUnitSq work1960.out = true := by decide +kernel

def cell1960 : CellCertificate where
  tauBall := tau1960
  contactCenter := center1960
  contactBall := contact1960
  work := work1960
  center_sq := center_sq1960
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1960.1
  jac_ok := checks1960.2.1
  accepted := checks1960.2.2

def tau1961 : RatBall :=
  ⟨⟨-79/320, 91/320⟩, 3/640⟩
def center1961 : GaussianRat :=
  ⟨-181318681/1000000000, 189181283/1000000000⟩
def contact1961 : RatBall := localContactBall tau1961 center1961
def work1961 : RoundedTauEval :=
  evalTau precision tau1961 contact1961 logTwoBall

theorem center_sq1961 : (center1961.re : ℝ)^2 +
    (center1961.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1961]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1961 : work1961.theta.ok = true ∧
    work1961.jac.invOK = true ∧ acceptsUnitSq work1961.out = true := by decide +kernel

def cell1961 : CellCertificate where
  tauBall := tau1961
  contactCenter := center1961
  contactBall := contact1961
  work := work1961
  center_sq := center_sq1961
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1961.1
  jac_ok := checks1961.2.1
  accepted := checks1961.2.2

def tau1962 : RatBall :=
  ⟨⟨-77/320, 91/320⟩, 3/640⟩
def center1962 : GaussianRat :=
  ⟨-17698031/100000000, 94910271/500000000⟩
def contact1962 : RatBall := localContactBall tau1962 center1962
def work1962 : RoundedTauEval :=
  evalTau precision tau1962 contact1962 logTwoBall

theorem center_sq1962 : (center1962.re : ℝ)^2 +
    (center1962.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1962]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1962 : work1962.theta.ok = true ∧
    work1962.jac.invOK = true ∧ acceptsUnitSq work1962.out = true := by decide +kernel

def cell1962 : CellCertificate where
  tauBall := tau1962
  contactCenter := center1962
  contactBall := contact1962
  work := work1962
  center_sq := center_sq1962
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1962.1
  jac_ok := checks1962.2.1
  accepted := checks1962.2.2

def tau1963 : RatBall :=
  ⟨⟨-15/64, 89/320⟩, 3/640⟩
def center1963 : GaussianRat :=
  ⟨-21501427/125000000, 186088727/1000000000⟩
def contact1963 : RatBall := localContactBall tau1963 center1963
def work1963 : RoundedTauEval :=
  evalTau precision tau1963 contact1963 logTwoBall

theorem center_sq1963 : (center1963.re : ℝ)^2 +
    (center1963.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1963]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1963 : work1963.theta.ok = true ∧
    work1963.jac.invOK = true ∧ acceptsUnitSq work1963.out = true := by decide +kernel

def cell1963 : CellCertificate where
  tauBall := tau1963
  contactCenter := center1963
  contactBall := contact1963
  work := work1963
  center_sq := center_sq1963
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1963.1
  jac_ok := checks1963.2.1
  accepted := checks1963.2.2

def tau1964 : RatBall :=
  ⟨⟨-73/320, 89/320⟩, 3/640⟩
def center1964 : GaussianRat :=
  ⟨-6705983/40000000, 46671637/250000000⟩
def contact1964 : RatBall := localContactBall tau1964 center1964
def work1964 : RoundedTauEval :=
  evalTau precision tau1964 contact1964 logTwoBall

theorem center_sq1964 : (center1964.re : ℝ)^2 +
    (center1964.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1964]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1964 : work1964.theta.ok = true ∧
    work1964.jac.invOK = true ∧ acceptsUnitSq work1964.out = true := by decide +kernel

def cell1964 : CellCertificate where
  tauBall := tau1964
  contactCenter := center1964
  contactBall := contact1964
  work := work1964
  center_sq := center_sq1964
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1964.1
  jac_ok := checks1964.2.1
  accepted := checks1964.2.2

def tau1965 : RatBall :=
  ⟨⟨-15/64, 91/320⟩, 3/640⟩
def center1965 : GaussianRat :=
  ⟨-34524793/200000000, 2380599/12500000⟩
def contact1965 : RatBall := localContactBall tau1965 center1965
def work1965 : RoundedTauEval :=
  evalTau precision tau1965 contact1965 logTwoBall

theorem center_sq1965 : (center1965.re : ℝ)^2 +
    (center1965.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1965]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1965 : work1965.theta.ok = true ∧
    work1965.jac.invOK = true ∧ acceptsUnitSq work1965.out = true := by decide +kernel

def cell1965 : CellCertificate where
  tauBall := tau1965
  contactCenter := center1965
  contactBall := contact1965
  work := work1965
  center_sq := center_sq1965
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1965.1
  jac_ok := checks1965.2.1
  accepted := checks1965.2.2

def tau1966 : RatBall :=
  ⟨⟨-73/320, 91/320⟩, 3/640⟩
def center1966 : GaussianRat :=
  ⟨-33649989/200000000, 38212623/200000000⟩
def contact1966 : RatBall := localContactBall tau1966 center1966
def work1966 : RoundedTauEval :=
  evalTau precision tau1966 contact1966 logTwoBall

theorem center_sq1966 : (center1966.re : ℝ)^2 +
    (center1966.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1966]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1966 : work1966.theta.ok = true ∧
    work1966.jac.invOK = true ∧ acceptsUnitSq work1966.out = true := by decide +kernel

def cell1966 : CellCertificate where
  tauBall := tau1966
  contactCenter := center1966
  contactBall := contact1966
  work := work1966
  center_sq := center_sq1966
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1966.1
  jac_ok := checks1966.2.1
  accepted := checks1966.2.2

def tau1967 : RatBall :=
  ⟨⟨-79/320, 93/320⟩, 3/640⟩
def center1967 : GaussianRat :=
  ⟨-90986481/500000000, 24189551/125000000⟩
def contact1967 : RatBall := localContactBall tau1967 center1967
def work1967 : RoundedTauEval :=
  evalTau precision tau1967 contact1967 logTwoBall

theorem center_sq1967 : (center1967.re : ℝ)^2 +
    (center1967.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1967]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1967 : work1967.theta.ok = true ∧
    work1967.jac.invOK = true ∧ acceptsUnitSq work1967.out = true := by decide +kernel

def cell1967 : CellCertificate where
  tauBall := tau1967
  contactCenter := center1967
  contactBall := contact1967
  work := work1967
  center_sq := center_sq1967
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1967.1
  jac_ok := checks1967.2.1
  accepted := checks1967.2.2

def cells : List CellCertificate := [cell1960, cell1961, cell1962, cell1963, cell1964, cell1965, cell1966, cell1967]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245

end


