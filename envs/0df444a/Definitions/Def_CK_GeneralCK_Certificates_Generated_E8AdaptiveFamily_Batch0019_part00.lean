-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0019_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0019_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:08:26.188981+00:00
-- url     : https://prove2.me/theorems/4e2ab869-ba71-4bdc-bd73-597a73f690d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0019 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0152 : RatBall :=
  ⟨⟨11/80, -13/80⟩, 3/160⟩
def center0152 : GaussianRat :=
  ⟨48637291/500000000, -111393603/1000000000⟩
def contact0152 : RatBall := localContactBall tau0152 center0152
def work0152 : RoundedTauEval :=
  evalTau precision tau0152 contact0152 logTwoBall

theorem center_sq0152 : (center0152.re : ℝ)^2 +
    (center0152.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0152]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0152 : work0152.theta.ok = true ∧
    work0152.jac.invOK = true ∧ acceptsUnitSq work0152.out = true := by decide +kernel

def cell0152 : CellCertificate where
  tauBall := tau0152
  contactCenter := center0152
  contactBall := contact0152
  work := work0152
  center_sq := center_sq0152
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0152.1
  jac_ok := checks0152.2.1
  accepted := checks0152.2.2

def tau0153 : RatBall :=
  ⟨⟨13/80, -3/16⟩, 3/160⟩
def center0153 : GaussianRat :=
  ⟨115659239/1000000000, -127856533/1000000000⟩
def contact0153 : RatBall := localContactBall tau0153 center0153
def work0153 : RoundedTauEval :=
  evalTau precision tau0153 contact0153 logTwoBall

theorem center_sq0153 : (center0153.re : ℝ)^2 +
    (center0153.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0153]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0153 : work0153.theta.ok = true ∧
    work0153.jac.invOK = true ∧ acceptsUnitSq work0153.out = true := by decide +kernel

def cell0153 : CellCertificate where
  tauBall := tau0153
  contactCenter := center0153
  contactBall := contact0153
  work := work0153
  center_sq := center_sq0153
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0153.1
  jac_ok := checks0153.2.1
  accepted := checks0153.2.2

def tau0154 : RatBall :=
  ⟨⟨3/16, -3/16⟩, 3/160⟩
def center0154 : GaussianRat :=
  ⟨132989007/1000000000, -15833617/125000000⟩
def contact0154 : RatBall := localContactBall tau0154 center0154
def work0154 : RoundedTauEval :=
  evalTau precision tau0154 contact0154 logTwoBall

theorem center_sq0154 : (center0154.re : ℝ)^2 +
    (center0154.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0154]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0154 : work0154.theta.ok = true ∧
    work0154.jac.invOK = true ∧ acceptsUnitSq work0154.out = true := by decide +kernel

def cell0154 : CellCertificate where
  tauBall := tau0154
  contactCenter := center0154
  contactBall := contact0154
  work := work0154
  center_sq := center_sq0154
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0154.1
  jac_ok := checks0154.2.1
  accepted := checks0154.2.2

def tau0155 : RatBall :=
  ⟨⟨13/80, -13/80⟩, 3/160⟩
def center0155 : GaussianRat :=
  ⟨114628827/1000000000, -110510723/1000000000⟩
def contact0155 : RatBall := localContactBall tau0155 center0155
def work0155 : RoundedTauEval :=
  evalTau precision tau0155 contact0155 logTwoBall

theorem center_sq0155 : (center0155.re : ℝ)^2 +
    (center0155.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0155]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0155 : work0155.theta.ok = true ∧
    work0155.jac.invOK = true ∧ acceptsUnitSq work0155.out = true := by decide +kernel

def cell0155 : CellCertificate where
  tauBall := tau0155
  contactCenter := center0155
  contactBall := contact0155
  work := work0155
  center_sq := center_sq0155
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0155.1
  jac_ok := checks0155.2.1
  accepted := checks0155.2.2

def tau0156 : RatBall :=
  ⟨⟨3/16, -13/80⟩, 3/160⟩
def center0156 : GaussianRat :=
  ⟨131822371/1000000000, -13687313/125000000⟩
def contact0156 : RatBall := localContactBall tau0156 center0156
def work0156 : RoundedTauEval :=
  evalTau precision tau0156 contact0156 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019


