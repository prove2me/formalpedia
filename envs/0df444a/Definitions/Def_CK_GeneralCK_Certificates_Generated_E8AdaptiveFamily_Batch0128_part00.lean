-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0128_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0128_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:16.115452+00:00
-- url     : https://prove2.me/theorems/e2534f54-d5ea-42ab-b884-60fb912994dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0128 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1024 : RatBall :=
  ⟨⟨49/160, 23/160⟩, 3/320⟩
def center1024 : GaussianRat :=
  ⟨209607093/1000000000, 22790011/250000000⟩
def contact1024 : RatBall := localContactBall tau1024 center1024
def work1024 : RoundedTauEval :=
  evalTau precision tau1024 contact1024 logTwoBall

theorem center_sq1024 : (center1024.re : ℝ)^2 +
    (center1024.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1024]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1024 : work1024.theta.ok = true ∧
    work1024.jac.invOK = true ∧ acceptsUnitSq work1024.out = true := by decide +kernel

def cell1024 : CellCertificate where
  tauBall := tau1024
  contactCenter := center1024
  contactBall := contact1024
  work := work1024
  center_sq := center_sq1024
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1024.1
  jac_ok := checks1024.2.1
  accepted := checks1024.2.2

def tau1025 : RatBall :=
  ⟨⟨51/160, 23/160⟩, 3/320⟩
def center1025 : GaussianRat :=
  ⟨6799051/31250000, 90469443/1000000000⟩
def contact1025 : RatBall := localContactBall tau1025 center1025
def work1025 : RoundedTauEval :=
  evalTau precision tau1025 contact1025 logTwoBall

theorem center_sq1025 : (center1025.re : ℝ)^2 +
    (center1025.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1025]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1025 : work1025.theta.ok = true ∧
    work1025.jac.invOK = true ∧ acceptsUnitSq work1025.out = true := by decide +kernel

def cell1025 : CellCertificate where
  tauBall := tau1025
  contactCenter := center1025
  contactBall := contact1025
  work := work1025
  center_sq := center_sq1025
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1025.1
  jac_ok := checks1025.2.1
  accepted := checks1025.2.2

def tau1026 : RatBall :=
  ⟨⟨53/160, 21/160⟩, 3/320⟩
def center1026 : GaussianRat :=
  ⟨224785281/1000000000, 4095231/50000000⟩
def contact1026 : RatBall := localContactBall tau1026 center1026
def work1026 : RoundedTauEval :=
  evalTau precision tau1026 contact1026 logTwoBall

theorem center_sq1026 : (center1026.re : ℝ)^2 +
    (center1026.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1026]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1026 : work1026.theta.ok = true ∧
    work1026.jac.invOK = true ∧ acceptsUnitSq work1026.out = true := by decide +kernel

def cell1026 : CellCertificate where
  tauBall := tau1026
  contactCenter := center1026
  contactBall := contact1026
  work := work1026
  center_sq := center_sq1026
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1026.1
  jac_ok := checks1026.2.1
  accepted := checks1026.2.2

def tau1027 : RatBall :=
  ⟨⟨11/32, 21/160⟩, 3/320⟩
def center1027 : GaussianRat :=
  ⟨232602861/1000000000, 81248009/1000000000⟩
def contact1027 : RatBall := localContactBall tau1027 center1027
def work1027 : RoundedTauEval :=
  evalTau precision tau1027 contact1027 logTwoBall

theorem center_sq1027 : (center1027.re : ℝ)^2 +
    (center1027.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1027]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1027 : work1027.theta.ok = true ∧
    work1027.jac.invOK = true ∧ acceptsUnitSq work1027.out = true := by decide +kernel

def cell1027 : CellCertificate where
  tauBall := tau1027
  contactCenter := center1027
  contactBall := contact1027
  work := work1027
  center_sq := center_sq1027
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1027.1
  jac_ok := checks1027.2.1
  accepted := checks1027.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128


