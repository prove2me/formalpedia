-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0149_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0149_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:22.48941+00:00
-- url     : https://prove2.me/theorems/b774b430-c76b-42b8-8464-3b64d892a88d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0149 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1192 : RatBall :=
  ⟨⟨41/160, 41/160⟩, 3/320⟩
def center1192 : GaussianRat :=
  ⟨184996961/1000000000, 21119029/125000000⟩
def contact1192 : RatBall := localContactBall tau1192 center1192
def work1192 : RoundedTauEval :=
  evalTau precision tau1192 contact1192 logTwoBall

theorem center_sq1192 : (center1192.re : ℝ)^2 +
    (center1192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1192 : work1192.theta.ok = true ∧
    work1192.jac.invOK = true ∧ acceptsUnitSq work1192.out = true := by decide +kernel

def cell1192 : CellCertificate where
  tauBall := tau1192
  contactCenter := center1192
  contactBall := contact1192
  work := work1192
  center_sq := center_sq1192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1192.1
  jac_ok := checks1192.2.1
  accepted := checks1192.2.2

def tau1193 : RatBall :=
  ⟨⟨43/160, 41/160⟩, 3/320⟩
def center1193 : GaussianRat :=
  ⟨193470247/1000000000, 167770653/1000000000⟩
def contact1193 : RatBall := localContactBall tau1193 center1193
def work1193 : RoundedTauEval :=
  evalTau precision tau1193 contact1193 logTwoBall

theorem center_sq1193 : (center1193.re : ℝ)^2 +
    (center1193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1193 : work1193.theta.ok = true ∧
    work1193.jac.invOK = true ∧ acceptsUnitSq work1193.out = true := by decide +kernel

def cell1193 : CellCertificate where
  tauBall := tau1193
  contactCenter := center1193
  contactBall := contact1193
  work := work1193
  center_sq := center_sq1193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1193.1
  jac_ok := checks1193.2.1
  accepted := checks1193.2.2

def tau1194 : RatBall :=
  ⟨⟨49/160, 33/160⟩, 3/320⟩
def center1194 : GaussianRat :=
  ⟨8553183/40000000, 26276749/200000000⟩
def contact1194 : RatBall := localContactBall tau1194 center1194
def work1194 : RoundedTauEval :=
  evalTau precision tau1194 contact1194 logTwoBall

theorem center_sq1194 : (center1194.re : ℝ)^2 +
    (center1194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1194 : work1194.theta.ok = true ∧
    work1194.jac.invOK = true ∧ acceptsUnitSq work1194.out = true := by decide +kernel

def cell1194 : CellCertificate where
  tauBall := tau1194
  contactCenter := center1194
  contactBall := contact1194
  work := work1194
  center_sq := center_sq1194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1194.1
  jac_ok := checks1194.2.1
  accepted := checks1194.2.2

def tau1195 : RatBall :=
  ⟨⟨51/160, 33/160⟩, 3/320⟩
def center1195 : GaussianRat :=
  ⟨13868507/62500000, 13035901/100000000⟩
def contact1195 : RatBall := localContactBall tau1195 center1195
def work1195 : RoundedTauEval :=
  evalTau precision tau1195 contact1195 logTwoBall

theorem center_sq1195 : (center1195.re : ℝ)^2 +
    (center1195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1195 : work1195.theta.ok = true ∧
    work1195.jac.invOK = true ∧ acceptsUnitSq work1195.out = true := by decide +kernel

def cell1195 : CellCertificate where
  tauBall := tau1195
  contactCenter := center1195
  contactBall := contact1195
  work := work1195
  center_sq := center_sq1195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1195.1
  jac_ok := checks1195.2.1
  accepted := checks1195.2.2

def tau1196 : RatBall :=
  ⟨⟨49/160, 7/32⟩, 3/320⟩
def center1196 : GaussianRat :=
  ⟨26859619/125000000, 139498183/1000000000⟩
def contact1196 : RatBall := localContactBall tau1196 center1196
def work1196 : RoundedTauEval :=
  evalTau precision tau1196 contact1196 logTwoBall

theorem center_sq1196 : (center1196.re : ℝ)^2 +
    (center1196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1196 : work1196.theta.ok = true ∧
    work1196.jac.invOK = true ∧ acceptsUnitSq work1196.out = true := by decide +kernel

def cell1196 : CellCertificate where
  tauBall := tau1196
  contactCenter := center1196
  contactBall := contact1196
  work := work1196
  center_sq := center_sq1196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1196.1
  jac_ok := checks1196.2.1
  accepted := checks1196.2.2

def tau1197 : RatBall :=
  ⟨⟨51/160, 7/32⟩, 3/320⟩
def center1197 : GaussianRat :=
  ⟨111484361/500000000, 13840239/100000000⟩
def contact1197 : RatBall := localContactBall tau1197 center1197
def work1197 : RoundedTauEval :=
  evalTau precision tau1197 contact1197 logTwoBall

theorem center_sq1197 : (center1197.re : ℝ)^2 +
    (center1197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1197]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149


