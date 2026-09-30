-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0086_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:42.668092+00:00
-- url     : https://prove2.me/theorems/aacc3c44-d197-40c8-8ec3-cfd6f9fb77d5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0086 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0688 : RatBall :=
  ⟨⟨47/160, -33/160⟩, 3/320⟩
def center0688 : GaussianRat :=
  ⟨205693537/1000000000, -132383201/1000000000⟩
def contact0688 : RatBall := localContactBall tau0688 center0688
def work0688 : RoundedTauEval :=
  evalTau precision tau0688 contact0688 logTwoBall

theorem center_sq0688 : (center0688.re : ℝ)^2 +
    (center0688.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0688]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0688 : work0688.theta.ok = true ∧
    work0688.jac.invOK = true ∧ acceptsUnitSq work0688.out = true := by decide +kernel

def cell0688 : CellCertificate where
  tauBall := tau0688
  contactCenter := center0688
  contactBall := contact0688
  work := work0688
  center_sq := center_sq0688
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0688.1
  jac_ok := checks0688.2.1
  accepted := checks0688.2.2

def tau0689 : RatBall :=
  ⟨⟨49/160, -37/160⟩, 3/320⟩
def center0689 : GaussianRat :=
  ⟨8639819/40000000, -36909857/250000000⟩
def contact0689 : RatBall := localContactBall tau0689 center0689
def work0689 : RoundedTauEval :=
  evalTau precision tau0689 contact0689 logTwoBall

theorem center_sq0689 : (center0689.re : ℝ)^2 +
    (center0689.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0689]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0689 : work0689.theta.ok = true ∧
    work0689.jac.invOK = true ∧ acceptsUnitSq work0689.out = true := by decide +kernel

def cell0689 : CellCertificate where
  tauBall := tau0689
  contactCenter := center0689
  contactBall := contact0689
  work := work0689
  center_sq := center_sq0689
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0689.1
  jac_ok := checks0689.2.1
  accepted := checks0689.2.2

def tau0690 : RatBall :=
  ⟨⟨49/160, -7/32⟩, 3/320⟩
def center0690 : GaussianRat :=
  ⟨26859619/125000000, -139498183/1000000000⟩
def contact0690 : RatBall := localContactBall tau0690 center0690
def work0690 : RoundedTauEval :=
  evalTau precision tau0690 contact0690 logTwoBall

theorem center_sq0690 : (center0690.re : ℝ)^2 +
    (center0690.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0690]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0690 : work0690.theta.ok = true ∧
    work0690.jac.invOK = true ∧ acceptsUnitSq work0690.out = true := by decide +kernel

def cell0690 : CellCertificate where
  tauBall := tau0690
  contactCenter := center0690
  contactBall := contact0690
  work := work0690
  center_sq := center_sq0690
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0690.1
  jac_ok := checks0690.2.1
  accepted := checks0690.2.2

def tau0691 : RatBall :=
  ⟨⟨51/160, -7/32⟩, 3/320⟩
def center0691 : GaussianRat :=
  ⟨111484361/500000000, -13840239/100000000⟩
def contact0691 : RatBall := localContactBall tau0691 center0691
def work0691 : RoundedTauEval :=
  evalTau precision tau0691 contact0691 logTwoBall

theorem center_sq0691 : (center0691.re : ℝ)^2 +
    (center0691.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0691]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0691 : work0691.theta.ok = true ∧
    work0691.jac.invOK = true ∧ acceptsUnitSq work0691.out = true := by decide +kernel

def cell0691 : CellCertificate where
  tauBall := tau0691
  contactCenter := center0691
  contactBall := contact0691
  work := work0691
  center_sq := center_sq0691
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0691.1
  jac_ok := checks0691.2.1
  accepted := checks0691.2.2

def tau0692 : RatBall :=
  ⟨⟨49/160, -33/160⟩, 3/320⟩
def center0692 : GaussianRat :=
  ⟨8553183/40000000, -26276749/200000000⟩
def contact0692 : RatBall := localContactBall tau0692 center0692
def work0692 : RoundedTauEval :=
  evalTau precision tau0692 contact0692 logTwoBall

theorem center_sq0692 : (center0692.re : ℝ)^2 +
    (center0692.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0692]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0692 : work0692.theta.ok = true ∧
    work0692.jac.invOK = true ∧ acceptsUnitSq work0692.out = true := by decide +kernel

def cell0692 : CellCertificate where
  tauBall := tau0692
  contactCenter := center0692
  contactBall := contact0692
  work := work0692
  center_sq := center_sq0692
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0692.1
  jac_ok := checks0692.2.1
  accepted := checks0692.2.2

def tau0693 : RatBall :=
  ⟨⟨51/160, -33/160⟩, 3/320⟩
def center0693 : GaussianRat :=
  ⟨13868507/62500000, -13035901/100000000⟩
def contact0693 : RatBall := localContactBall tau0693 center0693
def work0693 : RoundedTauEval :=
  evalTau precision tau0693 contact0693 logTwoBall

theorem center_sq0693 : (center0693.re : ℝ)^2 +
    (center0693.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0693]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086


