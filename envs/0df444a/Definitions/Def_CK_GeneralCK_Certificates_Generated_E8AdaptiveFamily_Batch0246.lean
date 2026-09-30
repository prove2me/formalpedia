-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0246
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0246
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:10:57.769308+00:00
-- url     : https://prove2.me/theorems/448202d9-7788-460d-888a-06748d3ccdd3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0246.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1968 : RatBall :=
  ⟨⟨-77/320, 93/320⟩, 3/640⟩
def center1968 : GaussianRat :=
  ⟨-44405679/250000000, 194173939/1000000000⟩
def contact1968 : RatBall := localContactBall tau1968 center1968
def work1968 : RoundedTauEval :=
  evalTau precision tau1968 contact1968 logTwoBall

theorem center_sq1968 : (center1968.re : ℝ)^2 +
    (center1968.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1968]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1968 : work1968.theta.ok = true ∧
    work1968.jac.invOK = true ∧ acceptsUnitSq work1968.out = true := by decide +kernel

def cell1968 : CellCertificate where
  tauBall := tau1968
  contactCenter := center1968
  contactBall := contact1968
  work := work1968
  center_sq := center_sq1968
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1968.1
  jac_ok := checks1968.2.1
  accepted := checks1968.2.2

def tau1969 : RatBall :=
  ⟨⟨-79/320, 19/64⟩, 3/640⟩
def center1969 : GaussianRat :=
  ⟨-91322907/500000000, 98931697/500000000⟩
def contact1969 : RatBall := localContactBall tau1969 center1969
def work1969 : RoundedTauEval :=
  evalTau precision tau1969 contact1969 logTwoBall

theorem center_sq1969 : (center1969.re : ℝ)^2 +
    (center1969.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1969]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1969 : work1969.theta.ok = true ∧
    work1969.jac.invOK = true ∧ acceptsUnitSq work1969.out = true := by decide +kernel

def cell1969 : CellCertificate where
  tauBall := tau1969
  contactCenter := center1969
  contactBall := contact1969
  work := work1969
  center_sq := center_sq1969
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1969.1
  jac_ok := checks1969.2.1
  accepted := checks1969.2.2

def tau1970 : RatBall :=
  ⟨⟨-77/320, 19/64⟩, 3/640⟩
def center1970 : GaussianRat :=
  ⟨-35656681/200000000, 198539511/1000000000⟩
def contact1970 : RatBall := localContactBall tau1970 center1970
def work1970 : RoundedTauEval :=
  evalTau precision tau1970 contact1970 logTwoBall

theorem center_sq1970 : (center1970.re : ℝ)^2 +
    (center1970.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1970]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1970 : work1970.theta.ok = true ∧
    work1970.jac.invOK = true ∧ acceptsUnitSq work1970.out = true := by decide +kernel

def cell1970 : CellCertificate where
  tauBall := tau1970
  contactCenter := center1970
  contactBall := contact1970
  work := work1970
  center_sq := center_sq1970
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1970.1
  jac_ok := checks1970.2.1
  accepted := checks1970.2.2

def tau1971 : RatBall :=
  ⟨⟨-15/64, 93/320⟩, 3/640⟩
def center1971 : GaussianRat :=
  ⟨-173254189/1000000000, 38963859/200000000⟩
def contact1971 : RatBall := localContactBall tau1971 center1971
def work1971 : RoundedTauEval :=
  evalTau precision tau1971 contact1971 logTwoBall

theorem center_sq1971 : (center1971.re : ℝ)^2 +
    (center1971.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1971]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1971 : work1971.theta.ok = true ∧
    work1971.jac.invOK = true ∧ acceptsUnitSq work1971.out = true := by decide +kernel

def cell1971 : CellCertificate where
  tauBall := tau1971
  contactCenter := center1971
  contactBall := contact1971
  work := work1971
  center_sq := center_sq1971
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1971.1
  jac_ok := checks1971.2.1
  accepted := checks1971.2.2

def tau1972 : RatBall :=
  ⟨⟨-73/320, 93/320⟩, 3/640⟩
def center1972 : GaussianRat :=
  ⟨-84433841/500000000, 195452163/1000000000⟩
def contact1972 : RatBall := localContactBall tau1972 center1972
def work1972 : RoundedTauEval :=
  evalTau precision tau1972 contact1972 logTwoBall

theorem center_sq1972 : (center1972.re : ℝ)^2 +
    (center1972.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1972]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1972 : work1972.theta.ok = true ∧
    work1972.jac.invOK = true ∧ acceptsUnitSq work1972.out = true := by decide +kernel

def cell1972 : CellCertificate where
  tauBall := tau1972
  contactCenter := center1972
  contactBall := contact1972
  work := work1972
  center_sq := center_sq1972
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1972.1
  jac_ok := checks1972.2.1
  accepted := checks1972.2.2

def tau1973 : RatBall :=
  ⟨⟨-15/64, 19/64⟩, 3/640⟩
def center1973 : GaussianRat :=
  ⟨-43475599/250000000, 199203157/1000000000⟩
def contact1973 : RatBall := localContactBall tau1973 center1973
def work1973 : RoundedTauEval :=
  evalTau precision tau1973 contact1973 logTwoBall

theorem center_sq1973 : (center1973.re : ℝ)^2 +
    (center1973.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1973]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1973 : work1973.theta.ok = true ∧
    work1973.jac.invOK = true ∧ acceptsUnitSq work1973.out = true := by decide +kernel

def cell1973 : CellCertificate where
  tauBall := tau1973
  contactCenter := center1973
  contactBall := contact1973
  work := work1973
  center_sq := center_sq1973
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1973.1
  jac_ok := checks1973.2.1
  accepted := checks1973.2.2

def tau1974 : RatBall :=
  ⟨⟨-73/320, 19/64⟩, 3/640⟩
def center1974 : GaussianRat :=
  ⟨-16950309/100000000, 199854009/1000000000⟩
def contact1974 : RatBall := localContactBall tau1974 center1974
def work1974 : RoundedTauEval :=
  evalTau precision tau1974 contact1974 logTwoBall

theorem center_sq1974 : (center1974.re : ℝ)^2 +
    (center1974.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1974]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1974 : work1974.theta.ok = true ∧
    work1974.jac.invOK = true ∧ acceptsUnitSq work1974.out = true := by decide +kernel

def cell1974 : CellCertificate where
  tauBall := tau1974
  contactCenter := center1974
  contactBall := contact1974
  work := work1974
  center_sq := center_sq1974
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1974.1
  jac_ok := checks1974.2.1
  accepted := checks1974.2.2

def tau1975 : RatBall :=
  ⟨⟨-71/320, 93/320⟩, 3/640⟩
def center1975 : GaussianRat :=
  ⟨-82231753/500000000, 98036117/500000000⟩
def contact1975 : RatBall := localContactBall tau1975 center1975
def work1975 : RoundedTauEval :=
  evalTau precision tau1975 contact1975 logTwoBall

theorem center_sq1975 : (center1975.re : ℝ)^2 +
    (center1975.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1975]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1975 : work1975.theta.ok = true ∧
    work1975.jac.invOK = true ∧ acceptsUnitSq work1975.out = true := by decide +kernel

def cell1975 : CellCertificate where
  tauBall := tau1975
  contactCenter := center1975
  contactBall := contact1975
  work := work1975
  center_sq := center_sq1975
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1975.1
  jac_ok := checks1975.2.1
  accepted := checks1975.2.2

def cells : List CellCertificate := [cell1968, cell1969, cell1970, cell1971, cell1972, cell1973, cell1974, cell1975]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246

end


