-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0214_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0214_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:25:04.902984+00:00
-- url     : https://prove2.me/theorems/71bd84b8-ac56-4c67-a729-7d25222831b6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0214 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1712 : RatBall :=
  ⟨⟨63/320, -21/64⟩, 3/640⟩
def center1712 : GaussianRat :=
  ⟨75163641/500000000, -225566837/1000000000⟩
def contact1712 : RatBall := localContactBall tau1712 center1712
def work1712 : RoundedTauEval :=
  evalTau precision tau1712 contact1712 logTwoBall

theorem center_sq1712 : (center1712.re : ℝ)^2 +
    (center1712.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1712]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1712 : work1712.theta.ok = true ∧
    work1712.jac.invOK = true ∧ acceptsUnitSq work1712.out = true := by decide +kernel

def cell1712 : CellCertificate where
  tauBall := tau1712
  contactCenter := center1712
  contactBall := contact1712
  work := work1712
  center_sq := center_sq1712
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1712.1
  jac_ok := checks1712.2.1
  accepted := checks1712.2.2

def tau1713 : RatBall :=
  ⟨⟨49/320, -103/320⟩, 3/640⟩
def center1713 : GaussianRat :=
  ⟨117379261/1000000000, -56270573/250000000⟩
def contact1713 : RatBall := localContactBall tau1713 center1713
def work1713 : RoundedTauEval :=
  evalTau precision tau1713 contact1713 logTwoBall

theorem center_sq1713 : (center1713.re : ℝ)^2 +
    (center1713.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1713 : work1713.theta.ok = true ∧
    work1713.jac.invOK = true ∧ acceptsUnitSq work1713.out = true := by decide +kernel

def cell1713 : CellCertificate where
  tauBall := tau1713
  contactCenter := center1713
  contactBall := contact1713
  work := work1713
  center_sq := center_sq1713
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1713.1
  jac_ok := checks1713.2.1
  accepted := checks1713.2.2

def tau1714 : RatBall :=
  ⟨⟨51/320, -103/320⟩, 3/640⟩
def center1714 : GaussianRat :=
  ⟨7627513/62500000, -224552577/1000000000⟩
def contact1714 : RatBall := localContactBall tau1714 center1714
def work1714 : RoundedTauEval :=
  evalTau precision tau1714 contact1714 logTwoBall

theorem center_sq1714 : (center1714.re : ℝ)^2 +
    (center1714.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1714]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1714 : work1714.theta.ok = true ∧
    work1714.jac.invOK = true ∧ acceptsUnitSq work1714.out = true := by decide +kernel

def cell1714 : CellCertificate where
  tauBall := tau1714
  contactCenter := center1714
  contactBall := contact1714
  work := work1714
  center_sq := center_sq1714
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1714.1
  jac_ok := checks1714.2.1
  accepted := checks1714.2.2

def tau1715 : RatBall :=
  ⟨⟨49/320, -101/320⟩, 3/640⟩
def center1715 : GaussianRat :=
  ⟨3652061/31250000, -220423219/1000000000⟩
def contact1715 : RatBall := localContactBall tau1715 center1715
def work1715 : RoundedTauEval :=
  evalTau precision tau1715 contact1715 logTwoBall

theorem center_sq1715 : (center1715.re : ℝ)^2 +
    (center1715.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1715]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1715 : work1715.theta.ok = true ∧
    work1715.jac.invOK = true ∧ acceptsUnitSq work1715.out = true := by decide +kernel

def cell1715 : CellCertificate where
  tauBall := tau1715
  contactCenter := center1715
  contactBall := contact1715
  work := work1715
  center_sq := center_sq1715
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1715.1
  jac_ok := checks1715.2.1
  accepted := checks1715.2.2

def tau1716 : RatBall :=
  ⟨⟨51/320, -101/320⟩, 3/640⟩
def center1716 : GaussianRat :=
  ⟨30377187/250000000, -6872127/31250000⟩
def contact1716 : RatBall := localContactBall tau1716 center1716
def work1716 : RoundedTauEval :=
  evalTau precision tau1716 contact1716 logTwoBall

theorem center_sq1716 : (center1716.re : ℝ)^2 +
    (center1716.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1716]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1716 : work1716.theta.ok = true ∧
    work1716.jac.invOK = true ∧ acceptsUnitSq work1716.out = true := by decide +kernel

def cell1716 : CellCertificate where
  tauBall := tau1716
  contactCenter := center1716
  contactBall := contact1716
  work := work1716
  center_sq := center_sq1716
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1716.1
  jac_ok := checks1716.2.1
  accepted := checks1716.2.2

def tau1717 : RatBall :=
  ⟨⟨53/320, -103/320⟩, 3/640⟩
def center1717 : GaussianRat :=
  ⟨126686203/1000000000, -224004631/1000000000⟩
def contact1717 : RatBall := localContactBall tau1717 center1717
def work1717 : RoundedTauEval :=
  evalTau precision tau1717 contact1717 logTwoBall

theorem center_sq1717 : (center1717.re : ℝ)^2 +
    (center1717.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1717]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1717 : work1717.theta.ok = true ∧
    work1717.jac.invOK = true ∧ acceptsUnitSq work1717.out = true := by decide +kernel

def cell1717 : CellCertificate where
  tauBall := tau1717
  contactCenter := center1717
  contactBall := contact1717
  work := work1717
  center_sq := center_sq1717
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1717.1
  jac_ok := checks1717.2.1
  accepted := checks1717.2.2

def tau1718 : RatBall :=
  ⟨⟨11/64, -103/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214


