-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0248_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:13.826234+00:00
-- url     : https://prove2.me/theorems/0a838979-15fc-4339-b22e-c4914ddc5987
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0248 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1984 : RatBall :=
  ⟨⟨-83/320, 97/320⟩, 3/640⟩
def center1984 : GaussianRat :=
  ⟨-9601467/50000000, 100397757/500000000⟩
def contact1984 : RatBall := localContactBall tau1984 center1984
def work1984 : RoundedTauEval :=
  evalTau precision tau1984 contact1984 logTwoBall

theorem center_sq1984 : (center1984.re : ℝ)^2 +
    (center1984.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1984]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1984 : work1984.theta.ok = true ∧
    work1984.jac.invOK = true ∧ acceptsUnitSq work1984.out = true := by decide +kernel

def cell1984 : CellCertificate where
  tauBall := tau1984
  contactCenter := center1984
  contactBall := contact1984
  work := work1984
  center_sq := center_sq1984
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1984.1
  jac_ok := checks1984.2.1
  accepted := checks1984.2.2

def tau1985 : RatBall :=
  ⟨⟨-81/320, 97/320⟩, 3/640⟩
def center1985 : GaussianRat :=
  ⟨-469233/2500000, 201515067/1000000000⟩
def contact1985 : RatBall := localContactBall tau1985 center1985
def work1985 : RoundedTauEval :=
  evalTau precision tau1985 contact1985 logTwoBall

theorem center_sq1985 : (center1985.re : ℝ)^2 +
    (center1985.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1985]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1985 : work1985.theta.ok = true ∧
    work1985.jac.invOK = true ∧ acceptsUnitSq work1985.out = true := by decide +kernel

def cell1985 : CellCertificate where
  tauBall := tau1985
  contactCenter := center1985
  contactBall := contact1985
  work := work1985
  center_sq := center_sq1985
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1985.1
  jac_ok := checks1985.2.1
  accepted := checks1985.2.2

def tau1986 : RatBall :=
  ⟨⟨-83/320, 99/320⟩, 3/640⟩
def center1986 : GaussianRat :=
  ⟨-19276477/100000000, 205127733/1000000000⟩
def contact1986 : RatBall := localContactBall tau1986 center1986
def work1986 : RoundedTauEval :=
  evalTau precision tau1986 contact1986 logTwoBall

theorem center_sq1986 : (center1986.re : ℝ)^2 +
    (center1986.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1986]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1986 : work1986.theta.ok = true ∧
    work1986.jac.invOK = true ∧ acceptsUnitSq work1986.out = true := by decide +kernel

def cell1986 : CellCertificate where
  tauBall := tau1986
  contactCenter := center1986
  contactBall := contact1986
  work := work1986
  center_sq := center_sq1986
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1986.1
  jac_ok := checks1986.2.1
  accepted := checks1986.2.2

def tau1987 : RatBall :=
  ⟨⟨-81/320, 99/320⟩, 3/640⟩
def center1987 : GaussianRat :=
  ⟨-47104143/250000000, 25733387/125000000⟩
def contact1987 : RatBall := localContactBall tau1987 center1987
def work1987 : RoundedTauEval :=
  evalTau precision tau1987 contact1987 logTwoBall

theorem center_sq1987 : (center1987.re : ℝ)^2 +
    (center1987.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1987]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1987 : work1987.theta.ok = true ∧
    work1987.jac.invOK = true ∧ acceptsUnitSq work1987.out = true := by decide +kernel

def cell1987 : CellCertificate where
  tauBall := tau1987
  contactCenter := center1987
  contactBall := contact1987
  work := work1987
  center_sq := center_sq1987
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1987.1
  jac_ok := checks1987.2.1
  accepted := checks1987.2.2

def tau1988 : RatBall :=
  ⟨⟨-79/320, 97/320⟩, 3/640⟩
def center1988 : GaussianRat :=
  ⟨-183337559/1000000000, 202222527/1000000000⟩
def contact1988 : RatBall := localContactBall tau1988 center1988
def work1988 : RoundedTauEval :=
  evalTau precision tau1988 contact1988 logTwoBall

theorem center_sq1988 : (center1988.re : ℝ)^2 +
    (center1988.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1988]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1988 : work1988.theta.ok = true ∧
    work1988.jac.invOK = true ∧ acceptsUnitSq work1988.out = true := by decide +kernel

def cell1988 : CellCertificate where
  tauBall := tau1988
  contactCenter := center1988
  contactBall := contact1988
  work := work1988
  center_sq := center_sq1988
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1988.1
  jac_ok := checks1988.2.1
  accepted := checks1988.2.2

def tau1989 : RatBall :=
  ⟨⟨-77/320, 97/320⟩, 3/640⟩
def center1989 : GaussianRat :=
  ⟨-35792539/200000000, 40583511/200000000⟩
def contact1989 : RatBall := localContactBall tau1989 center1989
def work1989 : RoundedTauEval :=
  evalTau precision tau1989 contact1989 logTwoBall

theorem center_sq1989 : (center1989.re : ℝ)^2 +
    (center1989.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1989]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1989 : work1989.theta.ok = true ∧
    work1989.jac.invOK = true ∧ acceptsUnitSq work1989.out = true := by decide +kernel

def cell1989 : CellCertificate where
  tauBall := tau1989
  contactCenter := center1989
  contactBall := contact1989
  work := work1989
  center_sq := center_sq1989
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1989.1
  jac_ok := checks1989.2.1
  accepted := checks1989.2.2

def tau1990 : RatBall :=
  ⟨⟨-79/320, 99/320⟩, 3/640⟩
def center1990 : GaussianRat :=
  ⟨-184048527/1000000000, 206594091/1000000000⟩
def contact1990 : RatBall := localContactBall tau1990 center1990

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248


