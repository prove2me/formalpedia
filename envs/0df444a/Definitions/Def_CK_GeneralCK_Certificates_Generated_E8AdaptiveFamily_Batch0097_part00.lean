-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0097_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0097_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:18:45.848933+00:00
-- url     : https://prove2.me/theorems/6186811c-53f3-4757-917a-593965fda529
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0097 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0776 : RatBall :=
  ⟨⟨-63/160, 9/160⟩, 3/320⟩
def center0776 : GaussianRat :=
  ⟨-65046299/250000000, 6715607/200000000⟩
def contact0776 : RatBall := localContactBall tau0776 center0776
def work0776 : RoundedTauEval :=
  evalTau precision tau0776 contact0776 logTwoBall

theorem center_sq0776 : (center0776.re : ℝ)^2 +
    (center0776.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0776]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0776 : work0776.theta.ok = true ∧
    work0776.jac.invOK = true ∧ acceptsUnitSq work0776.out = true := by decide +kernel

def cell0776 : CellCertificate where
  tauBall := tau0776
  contactCenter := center0776
  contactBall := contact0776
  work := work0776
  center_sq := center_sq0776
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0776.1
  jac_ok := checks0776.2.1
  accepted := checks0776.2.2

def tau0777 : RatBall :=
  ⟨⟨-61/160, 9/160⟩, 3/320⟩
def center0777 : GaussianRat :=
  ⟨-252683709/1000000000, 6774897/200000000⟩
def contact0777 : RatBall := localContactBall tau0777 center0777
def work0777 : RoundedTauEval :=
  evalTau precision tau0777 contact0777 logTwoBall

theorem center_sq0777 : (center0777.re : ℝ)^2 +
    (center0777.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0777]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0777 : work0777.theta.ok = true ∧
    work0777.jac.invOK = true ∧ acceptsUnitSq work0777.out = true := by decide +kernel

def cell0777 : CellCertificate where
  tauBall := tau0777
  contactCenter := center0777
  contactBall := contact0777
  work := work0777
  center_sq := center_sq0777
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0777.1
  jac_ok := checks0777.2.1
  accepted := checks0777.2.2

def tau0778 : RatBall :=
  ⟨⟨-63/160, 11/160⟩, 3/320⟩
def center0778 : GaussianRat :=
  ⟨-260517353/1000000000, 1026213/25000000⟩
def contact0778 : RatBall := localContactBall tau0778 center0778
def work0778 : RoundedTauEval :=
  evalTau precision tau0778 contact0778 logTwoBall

theorem center_sq0778 : (center0778.re : ℝ)^2 +
    (center0778.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0778]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0778 : work0778.theta.ok = true ∧
    work0778.jac.invOK = true ∧ acceptsUnitSq work0778.out = true := by decide +kernel

def cell0778 : CellCertificate where
  tauBall := tau0778
  contactCenter := center0778
  contactBall := contact0778
  work := work0778
  center_sq := center_sq0778
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0778.1
  jac_ok := checks0778.2.1
  accepted := checks0778.2.2

def tau0779 : RatBall :=
  ⟨⟨-61/160, 11/160⟩, 3/320⟩
def center0779 : GaussianRat :=
  ⟨-25301093/100000000, 41411583/1000000000⟩
def contact0779 : RatBall := localContactBall tau0779 center0779
def work0779 : RoundedTauEval :=
  evalTau precision tau0779 contact0779 logTwoBall

theorem center_sq0779 : (center0779.re : ℝ)^2 +
    (center0779.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0779]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0779 : work0779.theta.ok = true ∧
    work0779.jac.invOK = true ∧ acceptsUnitSq work0779.out = true := by decide +kernel

def cell0779 : CellCertificate where
  tauBall := tau0779
  contactCenter := center0779
  contactBall := contact0779
  work := work0779
  center_sq := center_sq0779
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0779.1
  jac_ok := checks0779.2.1
  accepted := checks0779.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097


