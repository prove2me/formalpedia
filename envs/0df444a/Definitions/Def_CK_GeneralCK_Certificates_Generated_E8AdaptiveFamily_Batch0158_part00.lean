-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0158_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0158_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:28:55.661848+00:00
-- url     : https://prove2.me/theorems/7599ca02-2bf2-47f4-9a0a-db807221c30b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0158 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1264 : RatBall :=
  ⟨⟨-21/64, -71/320⟩, 3/640⟩
def center1264 : GaussianRat :=
  ⟨-45854809/200000000, -139564933/1000000000⟩
def contact1264 : RatBall := localContactBall tau1264 center1264
def work1264 : RoundedTauEval :=
  evalTau precision tau1264 contact1264 logTwoBall

theorem center_sq1264 : (center1264.re : ℝ)^2 +
    (center1264.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1264]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1264 : work1264.theta.ok = true ∧
    work1264.jac.invOK = true ∧ acceptsUnitSq work1264.out = true := by decide +kernel

def cell1264 : CellCertificate where
  tauBall := tau1264
  contactCenter := center1264
  contactBall := contact1264
  work := work1264
  center_sq := center_sq1264
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1264.1
  jac_ok := checks1264.2.1
  accepted := checks1264.2.2

def tau1265 : RatBall :=
  ⟨⟨-107/320, -69/320⟩, 3/640⟩
def center1265 : GaussianRat :=
  ⟨-58174707/250000000, -67503627/500000000⟩
def contact1265 : RatBall := localContactBall tau1265 center1265
def work1265 : RoundedTauEval :=
  evalTau precision tau1265 contact1265 logTwoBall

theorem center_sq1265 : (center1265.re : ℝ)^2 +
    (center1265.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1265 : work1265.theta.ok = true ∧
    work1265.jac.invOK = true ∧ acceptsUnitSq work1265.out = true := by decide +kernel

def cell1265 : CellCertificate where
  tauBall := tau1265
  contactCenter := center1265
  contactBall := contact1265
  work := work1265
  center_sq := center_sq1265
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1265.1
  jac_ok := checks1265.2.1
  accepted := checks1265.2.2

def tau1266 : RatBall :=
  ⟨⟨-21/64, -69/320⟩, 3/640⟩
def center1266 : GaussianRat :=
  ⟨-57177633/250000000, -13556449/100000000⟩
def contact1266 : RatBall := localContactBall tau1266 center1266
def work1266 : RoundedTauEval :=
  evalTau precision tau1266 contact1266 logTwoBall

theorem center_sq1266 : (center1266.re : ℝ)^2 +
    (center1266.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1266]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1266 : work1266.theta.ok = true ∧
    work1266.jac.invOK = true ∧ acceptsUnitSq work1266.out = true := by decide +kernel

def cell1266 : CellCertificate where
  tauBall := tau1266
  contactCenter := center1266
  contactBall := contact1266
  work := work1266
  center_sq := center_sq1266
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1266.1
  jac_ok := checks1266.2.1
  accepted := checks1266.2.2

def tau1267 : RatBall :=
  ⟨⟨-109/320, -67/320⟩, 3/640⟩
def center1267 : GaussianRat :=
  ⟨-236112247/1000000000, -65243249/500000000⟩
def contact1267 : RatBall := localContactBall tau1267 center1267
def work1267 : RoundedTauEval :=
  evalTau precision tau1267 contact1267 logTwoBall

theorem center_sq1267 : (center1267.re : ℝ)^2 +
    (center1267.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1267]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1267 : work1267.theta.ok = true ∧
    work1267.jac.invOK = true ∧ acceptsUnitSq work1267.out = true := by decide +kernel

def cell1267 : CellCertificate where
  tauBall := tau1267
  contactCenter := center1267
  contactBall := contact1267
  work := work1267
  center_sq := center_sq1267
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1267.1
  jac_ok := checks1267.2.1
  accepted := checks1267.2.2

def tau1268 : RatBall :=
  ⟨⟨-111/320, -13/64⟩, 3/640⟩
def center1268 : GaussianRat :=
  ⟨-239515009/1000000000, -31500643/250000000⟩
def contact1268 : RatBall := localContactBall tau1268 center1268
def work1268 : RoundedTauEval :=
  evalTau precision tau1268 contact1268 logTwoBall

theorem center_sq1268 : (center1268.re : ℝ)^2 +
    (center1268.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1268]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1268 : work1268.theta.ok = true ∧
    work1268.jac.invOK = true ∧ acceptsUnitSq work1268.out = true := by decide +kernel

def cell1268 : CellCertificate where
  tauBall := tau1268
  contactCenter := center1268
  contactBall := contact1268
  work := work1268
  center_sq := center_sq1268
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1268.1
  jac_ok := checks1268.2.1
  accepted := checks1268.2.2

def tau1269 : RatBall :=
  ⟨⟨-109/320, -13/64⟩, 3/640⟩
def center1269 : GaussianRat :=
  ⟨-29446781/125000000, -63266993/500000000⟩
def contact1269 : RatBall := localContactBall tau1269 center1269
def work1269 : RoundedTauEval :=
  evalTau precision tau1269 contact1269 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158


