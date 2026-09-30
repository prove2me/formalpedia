-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0145_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0145_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:37:17.89278+00:00
-- url     : https://prove2.me/theorems/9b943007-f3df-41ce-bd7f-a4a2b769a03e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0145 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1160 : RatBall :=
  ⟨⟨7/32, 37/160⟩, 3/320⟩
def center1160 : GaussianRat :=
  ⟨78611951/500000000, 154924327/1000000000⟩
def contact1160 : RatBall := localContactBall tau1160 center1160
def work1160 : RoundedTauEval :=
  evalTau precision tau1160 contact1160 logTwoBall

theorem center_sq1160 : (center1160.re : ℝ)^2 +
    (center1160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1160 : work1160.theta.ok = true ∧
    work1160.jac.invOK = true ∧ acceptsUnitSq work1160.out = true := by decide +kernel

def cell1160 : CellCertificate where
  tauBall := tau1160
  contactCenter := center1160
  contactBall := contact1160
  work := work1160
  center_sq := center_sq1160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1160.1
  jac_ok := checks1160.2.1
  accepted := checks1160.2.2

def tau1161 : RatBall :=
  ⟨⟨33/160, 39/160⟩, 3/320⟩
def center1161 : GaussianRat :=
  ⟨18684153/125000000, 164515579/1000000000⟩
def contact1161 : RatBall := localContactBall tau1161 center1161
def work1161 : RoundedTauEval :=
  evalTau precision tau1161 contact1161 logTwoBall

theorem center_sq1161 : (center1161.re : ℝ)^2 +
    (center1161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1161 : work1161.theta.ok = true ∧
    work1161.jac.invOK = true ∧ acceptsUnitSq work1161.out = true := by decide +kernel

def cell1161 : CellCertificate where
  tauBall := tau1161
  contactCenter := center1161
  contactBall := contact1161
  work := work1161
  center_sq := center_sq1161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1161.1
  jac_ok := checks1161.2.1
  accepted := checks1161.2.2

def tau1162 : RatBall :=
  ⟨⟨7/32, 39/160⟩, 3/320⟩
def center1162 : GaussianRat :=
  ⟨9885359/62500000, 81782823/500000000⟩
def contact1162 : RatBall := localContactBall tau1162 center1162
def work1162 : RoundedTauEval :=
  evalTau precision tau1162 contact1162 logTwoBall

theorem center_sq1162 : (center1162.re : ℝ)^2 +
    (center1162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1162 : work1162.theta.ok = true ∧
    work1162.jac.invOK = true ∧ acceptsUnitSq work1162.out = true := by decide +kernel

def cell1162 : CellCertificate where
  tauBall := tau1162
  contactCenter := center1162
  contactBall := contact1162
  work := work1162
  center_sq := center_sq1162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1162.1
  jac_ok := checks1162.2.1
  accepted := checks1162.2.2

def tau1163 : RatBall :=
  ⟨⟨37/160, 37/160⟩, 3/320⟩
def center1163 : GaussianRat :=
  ⟨33162899/200000000, 153992113/1000000000⟩
def contact1163 : RatBall := localContactBall tau1163 center1163
def work1163 : RoundedTauEval :=
  evalTau precision tau1163 contact1163 logTwoBall

theorem center_sq1163 : (center1163.re : ℝ)^2 +
    (center1163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1163 : work1163.theta.ok = true ∧
    work1163.jac.invOK = true ∧ acceptsUnitSq work1163.out = true := by decide +kernel

def cell1163 : CellCertificate where
  tauBall := tau1163
  contactCenter := center1163
  contactBall := contact1163
  work := work1163
  center_sq := center_sq1163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1163.1
  jac_ok := checks1163.2.1
  accepted := checks1163.2.2

def tau1164 : RatBall :=
  ⟨⟨39/160, 37/160⟩, 3/320⟩
def center1164 : GaussianRat :=
  ⟨174343743/1000000000, 153020771/1000000000⟩
def contact1164 : RatBall := localContactBall tau1164 center1164
def work1164 : RoundedTauEval :=
  evalTau precision tau1164 contact1164 logTwoBall

theorem center_sq1164 : (center1164.re : ℝ)^2 +
    (center1164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1164]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145


