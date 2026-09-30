-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0249_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0249_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:51.092518+00:00
-- url     : https://prove2.me/theorems/0fd3c7de-18f8-4d1c-a6b9-3d21ba2dba22
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0249 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1992 : RatBall :=
  ⟨⟨-15/64, 97/320⟩, 3/640⟩
def center1992 : GaussianRat :=
  ⟨-87284451/500000000, 101799907/500000000⟩
def contact1992 : RatBall := localContactBall tau1992 center1992
def work1992 : RoundedTauEval :=
  evalTau precision tau1992 contact1992 logTwoBall

theorem center_sq1992 : (center1992.re : ℝ)^2 +
    (center1992.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1992]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1992 : work1992.theta.ok = true ∧
    work1992.jac.invOK = true ∧ acceptsUnitSq work1992.out = true := by decide +kernel

def cell1992 : CellCertificate where
  tauBall := tau1992
  contactCenter := center1992
  contactBall := contact1992
  work := work1992
  center_sq := center_sq1992
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1992.1
  jac_ok := checks1992.2.1
  accepted := checks1992.2.2

def tau1993 : RatBall :=
  ⟨⟨-73/320, 97/320⟩, 3/640⟩
def center1993 : GaussianRat :=
  ⟨-42539121/250000000, 204268971/1000000000⟩
def contact1993 : RatBall := localContactBall tau1993 center1993
def work1993 : RoundedTauEval :=
  evalTau precision tau1993 contact1993 logTwoBall

theorem center_sq1993 : (center1993.re : ℝ)^2 +
    (center1993.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1993]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1993 : work1993.theta.ok = true ∧
    work1993.jac.invOK = true ∧ acceptsUnitSq work1993.out = true := by decide +kernel

def cell1993 : CellCertificate where
  tauBall := tau1993
  contactCenter := center1993
  contactBall := contact1993
  work := work1993
  center_sq := center_sq1993
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1993.1
  jac_ok := checks1993.2.1
  accepted := checks1993.2.2

def tau1994 : RatBall :=
  ⟨⟨-15/64, 99/320⟩, 3/640⟩
def center1994 : GaussianRat :=
  ⟨-35050807/200000000, 8320383/40000000⟩
def contact1994 : RatBall := localContactBall tau1994 center1994
def work1994 : RoundedTauEval :=
  evalTau precision tau1994 contact1994 logTwoBall

theorem center_sq1994 : (center1994.re : ℝ)^2 +
    (center1994.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1994]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1994 : work1994.theta.ok = true ∧
    work1994.jac.invOK = true ∧ acceptsUnitSq work1994.out = true := by decide +kernel

def cell1994 : CellCertificate where
  tauBall := tau1994
  contactCenter := center1994
  contactBall := contact1994
  work := work1994
  center_sq := center_sq1994
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1994.1
  jac_ok := checks1994.2.1
  accepted := checks1994.2.2

def tau1995 : RatBall :=
  ⟨⟨-73/320, 99/320⟩, 3/640⟩
def center1995 : GaussianRat :=
  ⟨-42707047/250000000, 20869737/100000000⟩
def contact1995 : RatBall := localContactBall tau1995 center1995
def work1995 : RoundedTauEval :=
  evalTau precision tau1995 contact1995 logTwoBall

theorem center_sq1995 : (center1995.re : ℝ)^2 +
    (center1995.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1995]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1995 : work1995.theta.ok = true ∧
    work1995.jac.invOK = true ∧ acceptsUnitSq work1995.out = true := by decide +kernel

def cell1995 : CellCertificate where
  tauBall := tau1995
  contactCenter := center1995
  contactBall := contact1995
  work := work1995
  center_sq := center_sq1995
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1995.1
  jac_ok := checks1995.2.1
  accepted := checks1995.2.2

def tau1996 : RatBall :=
  ⟨⟨-79/320, 101/320⟩, 3/640⟩
def center1996 : GaussianRat :=
  ⟨-92389531/500000000, 210978373/1000000000⟩
def contact1996 : RatBall := localContactBall tau1996 center1996
def work1996 : RoundedTauEval :=
  evalTau precision tau1996 contact1996 logTwoBall

theorem center_sq1996 : (center1996.re : ℝ)^2 +
    (center1996.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1996]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1996 : work1996.theta.ok = true ∧
    work1996.jac.invOK = true ∧ acceptsUnitSq work1996.out = true := by decide +kernel

def cell1996 : CellCertificate where
  tauBall := tau1996
  contactCenter := center1996
  contactBall := contact1996
  work := work1996
  center_sq := center_sq1996
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1996.1
  jac_ok := checks1996.2.1
  accepted := checks1996.2.2

def tau1997 : RatBall :=
  ⟨⟨-77/320, 101/320⟩, 3/640⟩
def center1997 : GaussianRat :=
  ⟨-45094603/250000000, 105856123/500000000⟩
def contact1997 : RatBall := localContactBall tau1997 center1997
def work1997 : RoundedTauEval :=
  evalTau precision tau1997 contact1997 logTwoBall

theorem center_sq1997 : (center1997.re : ℝ)^2 +
    (center1997.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1997]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1997 : work1997.theta.ok = true ∧
    work1997.jac.invOK = true ∧ acceptsUnitSq work1997.out = true := by decide +kernel

def cell1997 : CellCertificate where
  tauBall := tau1997
  contactCenter := center1997
  contactBall := contact1997
  work := work1997
  center_sq := center_sq1997
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1997.1
  jac_ok := checks1997.2.1
  accepted := checks1997.2.2

def tau1998 : RatBall :=
  ⟨⟨-77/320, 103/320⟩, 3/640⟩
def center1998 : GaussianRat :=
  ⟨-36223107/200000000, 108064747/500000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249


