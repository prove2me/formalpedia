-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0247_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0247_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:39:34.169664+00:00
-- url     : https://prove2.me/theorems/254a8f14-ae3c-4149-9246-9d230c78c8da
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0247 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1976 : RatBall :=
  ⟨⟨-69/320, 93/320⟩, 3/640⟩
def center1976 : GaussianRat :=
  ⟨-32008397/200000000, 245849/1250000⟩
def contact1976 : RatBall := localContactBall tau1976 center1976
def work1976 : RoundedTauEval :=
  evalTau precision tau1976 contact1976 logTwoBall

theorem center_sq1976 : (center1976.re : ℝ)^2 +
    (center1976.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1976]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1976 : work1976.theta.ok = true ∧
    work1976.jac.invOK = true ∧ acceptsUnitSq work1976.out = true := by decide +kernel

def cell1976 : CellCertificate where
  tauBall := tau1976
  contactCenter := center1976
  contactBall := contact1976
  work := work1976
  center_sq := center_sq1976
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1976.1
  jac_ok := checks1976.2.1
  accepted := checks1976.2.2

def tau1977 : RatBall :=
  ⟨⟨-71/320, 19/64⟩, 3/640⟩
def center1977 : GaussianRat :=
  ⟨-165085801/1000000000, 40098349/200000000⟩
def contact1977 : RatBall := localContactBall tau1977 center1977
def work1977 : RoundedTauEval :=
  evalTau precision tau1977 contact1977 logTwoBall

theorem center_sq1977 : (center1977.re : ℝ)^2 +
    (center1977.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1977]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1977 : work1977.theta.ok = true ∧
    work1977.jac.invOK = true ∧ acceptsUnitSq work1977.out = true := by decide +kernel

def cell1977 : CellCertificate where
  tauBall := tau1977
  contactCenter := center1977
  contactBall := contact1977
  work := work1977
  center_sq := center_sq1977
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1977.1
  jac_ok := checks1977.2.1
  accepted := checks1977.2.2

def tau1978 : RatBall :=
  ⟨⟨-69/320, 19/64⟩, 3/640⟩
def center1978 : GaussianRat :=
  ⟨-80325427/500000000, 201116047/1000000000⟩
def contact1978 : RatBall := localContactBall tau1978 center1978
def work1978 : RoundedTauEval :=
  evalTau precision tau1978 contact1978 logTwoBall

theorem center_sq1978 : (center1978.re : ℝ)^2 +
    (center1978.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1978]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1978 : work1978.theta.ok = true ∧
    work1978.jac.invOK = true ∧ acceptsUnitSq work1978.out = true := by decide +kernel

def cell1978 : CellCertificate where
  tauBall := tau1978
  contactCenter := center1978
  contactBall := contact1978
  work := work1978
  center_sq := center_sq1978
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1978.1
  jac_ok := checks1978.2.1
  accepted := checks1978.2.2

def tau1979 : RatBall :=
  ⟨⟨-67/320, 93/320⟩, 3/640⟩
def center1979 : GaussianRat :=
  ⟨-3112069/20000000, 197272757/1000000000⟩
def contact1979 : RatBall := localContactBall tau1979 center1979
def work1979 : RoundedTauEval :=
  evalTau precision tau1979 contact1979 logTwoBall

theorem center_sq1979 : (center1979.re : ℝ)^2 +
    (center1979.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1979]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1979 : work1979.theta.ok = true ∧
    work1979.jac.invOK = true ∧ acceptsUnitSq work1979.out = true := by decide +kernel

def cell1979 : CellCertificate where
  tauBall := tau1979
  contactCenter := center1979
  contactBall := contact1979
  work := work1979
  center_sq := center_sq1979
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1979.1
  jac_ok := checks1979.2.1
  accepted := checks1979.2.2

def tau1980 : RatBall :=
  ⟨⟨-13/64, 93/320⟩, 3/640⟩
def center1980 : GaussianRat :=
  ⟨-151148249/1000000000, 98926301/500000000⟩
def contact1980 : RatBall := localContactBall tau1980 center1980
def work1980 : RoundedTauEval :=
  evalTau precision tau1980 contact1980 logTwoBall

theorem center_sq1980 : (center1980.re : ℝ)^2 +
    (center1980.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1980]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1980 : work1980.theta.ok = true ∧
    work1980.jac.invOK = true ∧ acceptsUnitSq work1980.out = true := by decide +kernel

def cell1980 : CellCertificate where
  tauBall := tau1980
  contactCenter := center1980
  contactBall := contact1980
  work := work1980
  center_sq := center_sq1980
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1980.1
  jac_ok := checks1980.2.1
  accepted := checks1980.2.2

def tau1981 : RatBall :=
  ⟨⟨-67/320, 19/64⟩, 3/640⟩
def center1981 : GaussianRat :=
  ⟨-78099293/500000000, 100863299/500000000⟩
def contact1981 : RatBall := localContactBall tau1981 center1981
def work1981 : RoundedTauEval :=
  evalTau precision tau1981 contact1981 logTwoBall

theorem center_sq1981 : (center1981.re : ℝ)^2 +
    (center1981.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1981]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247


