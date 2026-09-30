-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0198_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0198_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:08:24.72122+00:00
-- url     : https://prove2.me/theorems/2ab41e32-173a-4bbc-a8a5-f86a8601646c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0198 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1584 : RatBall :=
  ⟨⟨21/320, -121/320⟩, 3/640⟩
def center1584 : GaussianRat :=
  ⟨53251841/1000000000, -54951623/200000000⟩
def contact1584 : RatBall := localContactBall tau1584 center1584
def work1584 : RoundedTauEval :=
  evalTau precision tau1584 contact1584 logTwoBall

theorem center_sq1584 : (center1584.re : ℝ)^2 +
    (center1584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1584 : work1584.theta.ok = true ∧
    work1584.jac.invOK = true ∧ acceptsUnitSq work1584.out = true := by decide +kernel

def cell1584 : CellCertificate where
  tauBall := tau1584
  contactCenter := center1584
  contactBall := contact1584
  work := work1584
  center_sq := center_sq1584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1584.1
  jac_ok := checks1584.2.1
  accepted := checks1584.2.2

def tau1585 : RatBall :=
  ⟨⟨17/320, -119/320⟩, 3/640⟩
def center1585 : GaussianRat :=
  ⟨42909337/1000000000, -135131799/500000000⟩
def contact1585 : RatBall := localContactBall tau1585 center1585
def work1585 : RoundedTauEval :=
  evalTau precision tau1585 contact1585 logTwoBall

theorem center_sq1585 : (center1585.re : ℝ)^2 +
    (center1585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1585 : work1585.theta.ok = true ∧
    work1585.jac.invOK = true ∧ acceptsUnitSq work1585.out = true := by decide +kernel

def cell1585 : CellCertificate where
  tauBall := tau1585
  contactCenter := center1585
  contactBall := contact1585
  work := work1585
  center_sq := center_sq1585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1585.1
  jac_ok := checks1585.2.1
  accepted := checks1585.2.2

def tau1586 : RatBall :=
  ⟨⟨19/320, -119/320⟩, 3/640⟩
def center1586 : GaussianRat :=
  ⟨47935117/1000000000, -2109457/7812500⟩
def contact1586 : RatBall := localContactBall tau1586 center1586
def work1586 : RoundedTauEval :=
  evalTau precision tau1586 contact1586 logTwoBall

theorem center_sq1586 : (center1586.re : ℝ)^2 +
    (center1586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1586 : work1586.theta.ok = true ∧
    work1586.jac.invOK = true ∧ acceptsUnitSq work1586.out = true := by decide +kernel

def cell1586 : CellCertificate where
  tauBall := tau1586
  contactCenter := center1586
  contactBall := contact1586
  work := work1586
  center_sq := center_sq1586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1586.1
  jac_ok := checks1586.2.1
  accepted := checks1586.2.2

def tau1587 : RatBall :=
  ⟨⟨17/320, -117/320⟩, 3/640⟩
def center1587 : GaussianRat :=
  ⟨10668331/250000000, -265248069/1000000000⟩
def contact1587 : RatBall := localContactBall tau1587 center1587
def work1587 : RoundedTauEval :=
  evalTau precision tau1587 contact1587 logTwoBall

theorem center_sq1587 : (center1587.re : ℝ)^2 +
    (center1587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1587]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1587 : work1587.theta.ok = true ∧
    work1587.jac.invOK = true ∧ acceptsUnitSq work1587.out = true := by decide +kernel

def cell1587 : CellCertificate where
  tauBall := tau1587
  contactCenter := center1587
  contactBall := contact1587
  work := work1587
  center_sq := center_sq1587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1587.1
  jac_ok := checks1587.2.1
  accepted := checks1587.2.2

def tau1588 : RatBall :=
  ⟨⟨19/320, -117/320⟩, 3/640⟩
def center1588 : GaussianRat :=
  ⟨23835959/500000000, -265001899/1000000000⟩
def contact1588 : RatBall := localContactBall tau1588 center1588
def work1588 : RoundedTauEval :=
  evalTau precision tau1588 contact1588 logTwoBall

theorem center_sq1588 : (center1588.re : ℝ)^2 +
    (center1588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1588 : work1588.theta.ok = true ∧
    work1588.jac.invOK = true ∧ acceptsUnitSq work1588.out = true := by decide +kernel

def cell1588 : CellCertificate where
  tauBall := tau1588
  contactCenter := center1588
  contactBall := contact1588
  work := work1588
  center_sq := center_sq1588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1588.1
  jac_ok := checks1588.2.1
  accepted := checks1588.2.2

def tau1589 : RatBall :=
  ⟨⟨21/320, -119/320⟩, 3/640⟩
def center1589 : GaussianRat :=
  ⟨26476749/500000000, -33716241/125000000⟩
def contact1589 : RatBall := localContactBall tau1589 center1589
def work1589 : RoundedTauEval :=
  evalTau precision tau1589 contact1589 logTwoBall

theorem center_sq1589 : (center1589.re : ℝ)^2 +
    (center1589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1589 : work1589.theta.ok = true ∧
    work1589.jac.invOK = true ∧ acceptsUnitSq work1589.out = true := by decide +kernel

def cell1589 : CellCertificate where
  tauBall := tau1589
  contactCenter := center1589
  contactBall := contact1589
  work := work1589
  center_sq := center_sq1589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1589.1
  jac_ok := checks1589.2.1
  accepted := checks1589.2.2

def tau1590 : RatBall :=
  ⟨⟨23/320, -119/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198


