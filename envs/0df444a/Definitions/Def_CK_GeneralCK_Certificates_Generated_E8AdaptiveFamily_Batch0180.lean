-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0180
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0180
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:59:55.560622+00:00
-- url     : https://prove2.me/theorems/50df0778-fc4f-43ab-9f14-88014b129c09
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0180.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1440 : RatBall :=
  ⟨⟨-7/64, -111/320⟩, 3/640⟩
def center1440 : GaussianRat :=
  ⟨-85999463/1000000000, -247453051/1000000000⟩
def contact1440 : RatBall := localContactBall tau1440 center1440
def work1440 : RoundedTauEval :=
  evalTau precision tau1440 contact1440 logTwoBall

theorem center_sq1440 : (center1440.re : ℝ)^2 +
    (center1440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1440 : work1440.theta.ok = true ∧
    work1440.jac.invOK = true ∧ acceptsUnitSq work1440.out = true := by decide +kernel

def cell1440 : CellCertificate where
  tauBall := tau1440
  contactCenter := center1440
  contactBall := contact1440
  work := work1440
  center_sq := center_sq1440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1440.1
  jac_ok := checks1440.2.1
  accepted := checks1440.2.2

def tau1441 : RatBall :=
  ⟨⟨-33/320, -111/320⟩, 3/640⟩
def center1441 : GaussianRat :=
  ⟨-20287513/250000000, -247870587/1000000000⟩
def contact1441 : RatBall := localContactBall tau1441 center1441
def work1441 : RoundedTauEval :=
  evalTau precision tau1441 contact1441 logTwoBall

theorem center_sq1441 : (center1441.re : ℝ)^2 +
    (center1441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1441 : work1441.theta.ok = true ∧
    work1441.jac.invOK = true ∧ acceptsUnitSq work1441.out = true := by decide +kernel

def cell1441 : CellCertificate where
  tauBall := tau1441
  contactCenter := center1441
  contactBall := contact1441
  work := work1441
  center_sq := center_sq1441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1441.1
  jac_ok := checks1441.2.1
  accepted := checks1441.2.2

def tau1442 : RatBall :=
  ⟨⟨-7/64, -109/320⟩, 3/640⟩
def center1442 : GaussianRat :=
  ⟨-17115273/200000000, -242620769/1000000000⟩
def contact1442 : RatBall := localContactBall tau1442 center1442
def work1442 : RoundedTauEval :=
  evalTau precision tau1442 contact1442 logTwoBall

theorem center_sq1442 : (center1442.re : ℝ)^2 +
    (center1442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1442 : work1442.theta.ok = true ∧
    work1442.jac.invOK = true ∧ acceptsUnitSq work1442.out = true := by decide +kernel

def cell1442 : CellCertificate where
  tauBall := tau1442
  contactCenter := center1442
  contactBall := contact1442
  work := work1442
  center_sq := center_sq1442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1442.1
  jac_ok := checks1442.2.1
  accepted := checks1442.2.2

def tau1443 : RatBall :=
  ⟨⟨-33/320, -109/320⟩, 3/640⟩
def center1443 : GaussianRat :=
  ⟨-20187397/250000000, -48605377/200000000⟩
def contact1443 : RatBall := localContactBall tau1443 center1443
def work1443 : RoundedTauEval :=
  evalTau precision tau1443 contact1443 logTwoBall

theorem center_sq1443 : (center1443.re : ℝ)^2 +
    (center1443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1443]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1443 : work1443.theta.ok = true ∧
    work1443.jac.invOK = true ∧ acceptsUnitSq work1443.out = true := by decide +kernel

def cell1443 : CellCertificate where
  tauBall := tau1443
  contactCenter := center1443
  contactBall := contact1443
  work := work1443
  center_sq := center_sq1443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1443.1
  jac_ok := checks1443.2.1
  accepted := checks1443.2.2

def tau1444 : RatBall :=
  ⟨⟨-39/320, -107/320⟩, 3/640⟩
def center1444 : GaussianRat :=
  ⟨-23684951/250000000, -1184781/5000000⟩
def contact1444 : RatBall := localContactBall tau1444 center1444
def work1444 : RoundedTauEval :=
  evalTau precision tau1444 contact1444 logTwoBall

theorem center_sq1444 : (center1444.re : ℝ)^2 +
    (center1444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1444]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1444 : work1444.theta.ok = true ∧
    work1444.jac.invOK = true ∧ acceptsUnitSq work1444.out = true := by decide +kernel

def cell1444 : CellCertificate where
  tauBall := tau1444
  contactCenter := center1444
  contactBall := contact1444
  work := work1444
  center_sq := center_sq1444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1444.1
  jac_ok := checks1444.2.1
  accepted := checks1444.2.2

def tau1445 : RatBall :=
  ⟨⟨-37/320, -107/320⟩, 3/640⟩
def center1445 : GaussianRat :=
  ⟨-22489569/250000000, -47478823/200000000⟩
def contact1445 : RatBall := localContactBall tau1445 center1445
def work1445 : RoundedTauEval :=
  evalTau precision tau1445 contact1445 logTwoBall

theorem center_sq1445 : (center1445.re : ℝ)^2 +
    (center1445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1445 : work1445.theta.ok = true ∧
    work1445.jac.invOK = true ∧ acceptsUnitSq work1445.out = true := by decide +kernel

def cell1445 : CellCertificate where
  tauBall := tau1445
  contactCenter := center1445
  contactBall := contact1445
  work := work1445
  center_sq := center_sq1445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1445.1
  jac_ok := checks1445.2.1
  accepted := checks1445.2.2

def tau1446 : RatBall :=
  ⟨⟨-39/320, -21/64⟩, 3/640⟩
def center1446 : GaussianRat :=
  ⟨-94297493/1000000000, -185753/800000⟩
def contact1446 : RatBall := localContactBall tau1446 center1446
def work1446 : RoundedTauEval :=
  evalTau precision tau1446 contact1446 logTwoBall

theorem center_sq1446 : (center1446.re : ℝ)^2 +
    (center1446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1446 : work1446.theta.ok = true ∧
    work1446.jac.invOK = true ∧ acceptsUnitSq work1446.out = true := by decide +kernel

def cell1446 : CellCertificate where
  tauBall := tau1446
  contactCenter := center1446
  contactBall := contact1446
  work := work1446
  center_sq := center_sq1446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1446.1
  jac_ok := checks1446.2.1
  accepted := checks1446.2.2

def tau1447 : RatBall :=
  ⟨⟨-37/320, -21/64⟩, 3/640⟩
def center1447 : GaussianRat :=
  ⟨-89536891/1000000000, -116308561/500000000⟩
def contact1447 : RatBall := localContactBall tau1447 center1447
def work1447 : RoundedTauEval :=
  evalTau precision tau1447 contact1447 logTwoBall

theorem center_sq1447 : (center1447.re : ℝ)^2 +
    (center1447.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1447]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1447 : work1447.theta.ok = true ∧
    work1447.jac.invOK = true ∧ acceptsUnitSq work1447.out = true := by decide +kernel

def cell1447 : CellCertificate where
  tauBall := tau1447
  contactCenter := center1447
  contactBall := contact1447
  work := work1447
  center_sq := center_sq1447
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1447.1
  jac_ok := checks1447.2.1
  accepted := checks1447.2.2

def cells : List CellCertificate := [cell1440, cell1441, cell1442, cell1443, cell1444, cell1445, cell1446, cell1447]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180

end


