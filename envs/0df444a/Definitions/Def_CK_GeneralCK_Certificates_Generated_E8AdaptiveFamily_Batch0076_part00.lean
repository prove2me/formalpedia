-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0076_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0076_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:20.108528+00:00
-- url     : https://prove2.me/theorems/03470a76-aa74-44b2-9388-69b24b3f4afc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0076 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0608 : RatBall :=
  ⟨⟨17/160, -9/32⟩, 3/320⟩
def center0608 : GaussianRat :=
  ⟨19945259/250000000, -39579621/200000000⟩
def contact0608 : RatBall := localContactBall tau0608 center0608
def work0608 : RoundedTauEval :=
  evalTau precision tau0608 contact0608 logTwoBall

theorem center_sq0608 : (center0608.re : ℝ)^2 +
    (center0608.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0608]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0608 : work0608.theta.ok = true ∧
    work0608.jac.invOK = true ∧ acceptsUnitSq work0608.out = true := by decide +kernel

def cell0608 : CellCertificate where
  tauBall := tau0608
  contactCenter := center0608
  contactBall := contact0608
  work := work0608
  center_sq := center_sq0608
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0608.1
  jac_ok := checks0608.2.1
  accepted := checks0608.2.2

def tau0609 : RatBall :=
  ⟨⟨19/160, -9/32⟩, 3/320⟩
def center0609 : GaussianRat :=
  ⟨22260513/250000000, -49311287/250000000⟩
def contact0609 : RatBall := localContactBall tau0609 center0609
def work0609 : RoundedTauEval :=
  evalTau precision tau0609 contact0609 logTwoBall

theorem center_sq0609 : (center0609.re : ℝ)^2 +
    (center0609.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0609]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0609 : work0609.theta.ok = true ∧
    work0609.jac.invOK = true ∧ acceptsUnitSq work0609.out = true := by decide +kernel

def cell0609 : CellCertificate where
  tauBall := tau0609
  contactCenter := center0609
  contactBall := contact0609
  work := work0609
  center_sq := center_sq0609
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0609.1
  jac_ok := checks0609.2.1
  accepted := checks0609.2.2

def tau0610 : RatBall :=
  ⟨⟨21/160, -47/160⟩, 3/320⟩
def center0610 : GaussianRat :=
  ⟨618987/6250000, -102878573/500000000⟩
def contact0610 : RatBall := localContactBall tau0610 center0610
def work0610 : RoundedTauEval :=
  evalTau precision tau0610 contact0610 logTwoBall

theorem center_sq0610 : (center0610.re : ℝ)^2 +
    (center0610.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0610]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0610 : work0610.theta.ok = true ∧
    work0610.jac.invOK = true ∧ acceptsUnitSq work0610.out = true := by decide +kernel

def cell0610 : CellCertificate where
  tauBall := tau0610
  contactCenter := center0610
  contactBall := contact0610
  work := work0610
  center_sq := center_sq0610
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0610.1
  jac_ok := checks0610.2.1
  accepted := checks0610.2.2

def tau0611 : RatBall :=
  ⟨⟨23/160, -47/160⟩, 3/320⟩
def center0611 : GaussianRat :=
  ⟨108280123/1000000000, -204924443/1000000000⟩
def contact0611 : RatBall := localContactBall tau0611 center0611
def work0611 : RoundedTauEval :=
  evalTau precision tau0611 contact0611 logTwoBall

theorem center_sq0611 : (center0611.re : ℝ)^2 +
    (center0611.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0611]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0611 : work0611.theta.ok = true ∧
    work0611.jac.invOK = true ∧ acceptsUnitSq work0611.out = true := by decide +kernel

def cell0611 : CellCertificate where
  tauBall := tau0611
  contactCenter := center0611
  contactBall := contact0611
  work := work0611
  center_sq := center_sq0611
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0611.1
  jac_ok := checks0611.2.1
  accepted := checks0611.2.2

def tau0612 : RatBall :=
  ⟨⟨21/160, -9/32⟩, 3/320⟩
def center0612 : GaussianRat :=
  ⟨2456559/25000000, -19652513/100000000⟩
def contact0612 : RatBall := localContactBall tau0612 center0612
def work0612 : RoundedTauEval :=
  evalTau precision tau0612 contact0612 logTwoBall

theorem center_sq0612 : (center0612.re : ℝ)^2 +
    (center0612.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0612]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0612 : work0612.theta.ok = true ∧
    work0612.jac.invOK = true ∧ acceptsUnitSq work0612.out = true := by decide +kernel

def cell0612 : CellCertificate where
  tauBall := tau0612
  contactCenter := center0612
  contactBall := contact0612
  work := work0612
  center_sq := center_sq0612
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0612.1
  jac_ok := checks0612.2.1
  accepted := checks0612.2.2

def tau0613 : RatBall :=
  ⟨⟨23/160, -9/32⟩, 3/320⟩
def center0613 : GaussianRat :=
  ⟨107438161/1000000000, -195739697/1000000000⟩
def contact0613 : RatBall := localContactBall tau0613 center0613
def work0613 : RoundedTauEval :=
  evalTau precision tau0613 contact0613 logTwoBall

theorem center_sq0613 : (center0613.re : ℝ)^2 +
    (center0613.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0613]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0613 : work0613.theta.ok = true ∧
    work0613.jac.invOK = true ∧ acceptsUnitSq work0613.out = true := by decide +kernel

def cell0613 : CellCertificate where
  tauBall := tau0613
  contactCenter := center0613
  contactBall := contact0613
  work := work0613
  center_sq := center_sq0613
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0613.1
  jac_ok := checks0613.2.1
  accepted := checks0613.2.2

def tau0614 : RatBall :=
  ⟨⟨17/160, -43/160⟩, 3/320⟩
def center0614 : GaussianRat :=
  ⟨39590143/500000000, -47162917/250000000⟩
def contact0614 : RatBall := localContactBall tau0614 center0614
def work0614 : RoundedTauEval :=
  evalTau precision tau0614 contact0614 logTwoBall

theorem center_sq0614 : (center0614.re : ℝ)^2 +
    (center0614.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0614]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076


