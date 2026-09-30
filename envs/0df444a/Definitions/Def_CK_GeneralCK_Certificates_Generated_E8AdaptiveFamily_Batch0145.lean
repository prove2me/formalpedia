-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0145
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0145
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:25:52.559664+00:00
-- url     : https://prove2.me/theorems/9b0e759d-a2ee-47e1-85fc-748bb8be6104
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0145.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0145_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1164 : work1164.theta.ok = true ∧
    work1164.jac.invOK = true ∧ acceptsUnitSq work1164.out = true := by decide +kernel

def cell1164 : CellCertificate where
  tauBall := tau1164
  contactCenter := center1164
  contactBall := contact1164
  work := work1164
  center_sq := center_sq1164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1164.1
  jac_ok := checks1164.2.1
  accepted := checks1164.2.2

def tau1165 : RatBall :=
  ⟨⟨37/160, 39/160⟩, 3/320⟩
def center1165 : GaussianRat :=
  ⟨83398769/500000000, 20321547/125000000⟩
def contact1165 : RatBall := localContactBall tau1165 center1165
def work1165 : RoundedTauEval :=
  evalTau precision tau1165 contact1165 logTwoBall

theorem center_sq1165 : (center1165.re : ℝ)^2 +
    (center1165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1165 : work1165.theta.ok = true ∧
    work1165.jac.invOK = true ∧ acceptsUnitSq work1165.out = true := by decide +kernel

def cell1165 : CellCertificate where
  tauBall := tau1165
  contactCenter := center1165
  contactBall := contact1165
  work := work1165
  center_sq := center_sq1165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1165.1
  jac_ok := checks1165.2.1
  accepted := checks1165.2.2

def tau1166 : RatBall :=
  ⟨⟨39/160, 39/160⟩, 3/320⟩
def center1166 : GaussianRat :=
  ⟨7014647/40000000, 32307527/200000000⟩
def contact1166 : RatBall := localContactBall tau1166 center1166
def work1166 : RoundedTauEval :=
  evalTau precision tau1166 contact1166 logTwoBall

theorem center_sq1166 : (center1166.re : ℝ)^2 +
    (center1166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1166 : work1166.theta.ok = true ∧
    work1166.jac.invOK = true ∧ acceptsUnitSq work1166.out = true := by decide +kernel

def cell1166 : CellCertificate where
  tauBall := tau1166
  contactCenter := center1166
  contactBall := contact1166
  work := work1166
  center_sq := center_sq1166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1166.1
  jac_ok := checks1166.2.1
  accepted := checks1166.2.2

def tau1167 : RatBall :=
  ⟨⟨41/160, 33/160⟩, 3/320⟩
def center1167 : GaussianRat :=
  ⟨180884951/1000000000, 135214257/1000000000⟩
def contact1167 : RatBall := localContactBall tau1167 center1167
def work1167 : RoundedTauEval :=
  evalTau precision tau1167 contact1167 logTwoBall

theorem center_sq1167 : (center1167.re : ℝ)^2 +
    (center1167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1167 : work1167.theta.ok = true ∧
    work1167.jac.invOK = true ∧ acceptsUnitSq work1167.out = true := by decide +kernel

def cell1167 : CellCertificate where
  tauBall := tau1167
  contactCenter := center1167
  contactBall := contact1167
  work := work1167
  center_sq := center_sq1167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1167.1
  jac_ok := checks1167.2.1
  accepted := checks1167.2.2

def cells : List CellCertificate := [cell1160, cell1161, cell1162, cell1163, cell1164, cell1165, cell1166, cell1167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145


