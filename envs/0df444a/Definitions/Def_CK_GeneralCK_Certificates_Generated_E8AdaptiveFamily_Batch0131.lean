-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0131
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0131
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:42:20.968549+00:00
-- url     : https://prove2.me/theorems/0d418137-7bd4-459b-920f-19258bc3b999
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0131.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1048 : RatBall :=
  ⟨⟨53/160, 27/160⟩, 3/320⟩
def center1048 : GaussianRat :=
  ⟨113515613/500000000, 13190697/125000000⟩
def contact1048 : RatBall := localContactBall tau1048 center1048
def work1048 : RoundedTauEval :=
  evalTau precision tau1048 contact1048 logTwoBall

theorem center_sq1048 : (center1048.re : ℝ)^2 +
    (center1048.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1048]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1048 : work1048.theta.ok = true ∧
    work1048.jac.invOK = true ∧ acceptsUnitSq work1048.out = true := by decide +kernel

def cell1048 : CellCertificate where
  tauBall := tau1048
  contactCenter := center1048
  contactBall := contact1048
  work := work1048
  center_sq := center_sq1048
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1048.1
  jac_ok := checks1048.2.1
  accepted := checks1048.2.2

def tau1049 : RatBall :=
  ⟨⟨11/32, 27/160⟩, 3/320⟩
def center1049 : GaussianRat :=
  ⟨234895911/1000000000, 52333711/500000000⟩
def contact1049 : RatBall := localContactBall tau1049 center1049
def work1049 : RoundedTauEval :=
  evalTau precision tau1049 contact1049 logTwoBall

theorem center_sq1049 : (center1049.re : ℝ)^2 +
    (center1049.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1049]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1049 : work1049.theta.ok = true ∧
    work1049.jac.invOK = true ∧ acceptsUnitSq work1049.out = true := by decide +kernel

def cell1049 : CellCertificate where
  tauBall := tau1049
  contactCenter := center1049
  contactBall := contact1049
  work := work1049
  center_sq := center_sq1049
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1049.1
  jac_ok := checks1049.2.1
  accepted := checks1049.2.2

def tau1050 : RatBall :=
  ⟨⟨49/160, 29/160⟩, 3/320⟩
def center1050 : GaussianRat :=
  ⟨52985469/250000000, 115229173/1000000000⟩
def contact1050 : RatBall := localContactBall tau1050 center1050
def work1050 : RoundedTauEval :=
  evalTau precision tau1050 contact1050 logTwoBall

theorem center_sq1050 : (center1050.re : ℝ)^2 +
    (center1050.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1050]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1050 : work1050.theta.ok = true ∧
    work1050.jac.invOK = true ∧ acceptsUnitSq work1050.out = true := by decide +kernel

def cell1050 : CellCertificate where
  tauBall := tau1050
  contactCenter := center1050
  contactBall := contact1050
  work := work1050
  center_sq := center_sq1050
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1050.1
  jac_ok := checks1050.2.1
  accepted := checks1050.2.2

def tau1051 : RatBall :=
  ⟨⟨51/160, 29/160⟩, 3/320⟩
def center1051 : GaussianRat :=
  ⟨429614/1953125, 114341983/1000000000⟩
def contact1051 : RatBall := localContactBall tau1051 center1051
def work1051 : RoundedTauEval :=
  evalTau precision tau1051 contact1051 logTwoBall

theorem center_sq1051 : (center1051.re : ℝ)^2 +
    (center1051.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1051]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1051 : work1051.theta.ok = true ∧
    work1051.jac.invOK = true ∧ acceptsUnitSq work1051.out = true := by decide +kernel

def cell1051 : CellCertificate where
  tauBall := tau1051
  contactCenter := center1051
  contactBall := contact1051
  work := work1051
  center_sq := center_sq1051
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1051.1
  jac_ok := checks1051.2.1
  accepted := checks1051.2.2

def tau1052 : RatBall :=
  ⟨⟨49/160, 31/160⟩, 3/320⟩
def center1052 : GaussianRat :=
  ⟨106425859/500000000, 123294587/1000000000⟩
def contact1052 : RatBall := localContactBall tau1052 center1052
def work1052 : RoundedTauEval :=
  evalTau precision tau1052 contact1052 logTwoBall

theorem center_sq1052 : (center1052.re : ℝ)^2 +
    (center1052.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1052]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1052 : work1052.theta.ok = true ∧
    work1052.jac.invOK = true ∧ acceptsUnitSq work1052.out = true := by decide +kernel

def cell1052 : CellCertificate where
  tauBall := tau1052
  contactCenter := center1052
  contactBall := contact1052
  work := work1052
  center_sq := center_sq1052
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1052.1
  jac_ok := checks1052.2.1
  accepted := checks1052.2.2

def tau1053 : RatBall :=
  ⟨⟨51/160, 31/160⟩, 3/320⟩
def center1053 : GaussianRat :=
  ⟨110447247/500000000, 61169673/500000000⟩
def contact1053 : RatBall := localContactBall tau1053 center1053
def work1053 : RoundedTauEval :=
  evalTau precision tau1053 contact1053 logTwoBall

theorem center_sq1053 : (center1053.re : ℝ)^2 +
    (center1053.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1053]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1053 : work1053.theta.ok = true ∧
    work1053.jac.invOK = true ∧ acceptsUnitSq work1053.out = true := by decide +kernel

def cell1053 : CellCertificate where
  tauBall := tau1053
  contactCenter := center1053
  contactBall := contact1053
  work := work1053
  center_sq := center_sq1053
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1053.1
  jac_ok := checks1053.2.1
  accepted := checks1053.2.2

def tau1054 : RatBall :=
  ⟨⟨53/160, 29/160⟩, 3/320⟩
def center1054 : GaussianRat :=
  ⟨227914773/1000000000, 56716957/500000000⟩
def contact1054 : RatBall := localContactBall tau1054 center1054
def work1054 : RoundedTauEval :=
  evalTau precision tau1054 contact1054 logTwoBall

theorem center_sq1054 : (center1054.re : ℝ)^2 +
    (center1054.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1054]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1054 : work1054.theta.ok = true ∧
    work1054.jac.invOK = true ∧ acceptsUnitSq work1054.out = true := by decide +kernel

def cell1054 : CellCertificate where
  tauBall := tau1054
  contactCenter := center1054
  contactBall := contact1054
  work := work1054
  center_sq := center_sq1054
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1054.1
  jac_ok := checks1054.2.1
  accepted := checks1054.2.2

def tau1055 : RatBall :=
  ⟨⟨11/32, 29/160⟩, 3/320⟩
def center1055 : GaussianRat :=
  ⟨117898859/500000000, 112506293/1000000000⟩
def contact1055 : RatBall := localContactBall tau1055 center1055
def work1055 : RoundedTauEval :=
  evalTau precision tau1055 contact1055 logTwoBall

theorem center_sq1055 : (center1055.re : ℝ)^2 +
    (center1055.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1055]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1055 : work1055.theta.ok = true ∧
    work1055.jac.invOK = true ∧ acceptsUnitSq work1055.out = true := by decide +kernel

def cell1055 : CellCertificate where
  tauBall := tau1055
  contactCenter := center1055
  contactBall := contact1055
  work := work1055
  center_sq := center_sq1055
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1055.1
  jac_ok := checks1055.2.1
  accepted := checks1055.2.2

def cells : List CellCertificate := [cell1048, cell1049, cell1050, cell1051, cell1052, cell1053, cell1054, cell1055]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131

end


