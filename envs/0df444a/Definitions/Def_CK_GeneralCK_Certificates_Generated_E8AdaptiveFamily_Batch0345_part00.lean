-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0345_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0345_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:52:14.159914+00:00
-- url     : https://prove2.me/theorems/cdf31a98-c488-4e1c-8caa-a7afdfec6282
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0345 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2760 : RatBall :=
  ⟨⟨-53/640, -241/640⟩, 3/1280⟩
def center2760 : GaussianRat :=
  ⟨-13397789/200000000, -54513591/200000000⟩
def contact2760 : RatBall := localContactBall tau2760 center2760
def work2760 : RoundedTauEval :=
  evalTau precision tau2760 contact2760 logTwoBall

theorem center_sq2760 : (center2760.re : ℝ)^2 +
    (center2760.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2760]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2760 : work2760.theta.ok = true ∧
    work2760.jac.invOK = true ∧ acceptsUnitSq work2760.out = true := by decide +kernel

def cell2760 : CellCertificate where
  tauBall := tau2760
  contactCenter := center2760
  contactBall := contact2760
  work := work2760
  center_sq := center_sq2760
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2760.1
  jac_ok := checks2760.2.1
  accepted := checks2760.2.2

def tau2761 : RatBall :=
  ⟨⟨-51/640, -243/640⟩, 3/1280⟩
def center2761 : GaussianRat :=
  ⟨-32332713/500000000, -275263239/1000000000⟩
def contact2761 : RatBall := localContactBall tau2761 center2761
def work2761 : RoundedTauEval :=
  evalTau precision tau2761 contact2761 logTwoBall

theorem center_sq2761 : (center2761.re : ℝ)^2 +
    (center2761.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2761]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2761 : work2761.theta.ok = true ∧
    work2761.jac.invOK = true ∧ acceptsUnitSq work2761.out = true := by decide +kernel

def cell2761 : CellCertificate where
  tauBall := tau2761
  contactCenter := center2761
  contactBall := contact2761
  work := work2761
  center_sq := center_sq2761
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2761.1
  jac_ok := checks2761.2.1
  accepted := checks2761.2.2

def tau2762 : RatBall :=
  ⟨⟨-49/640, -243/640⟩, 3/1280⟩
def center2762 : GaussianRat :=
  ⟨-12430013/200000000, -275443499/1000000000⟩
def contact2762 : RatBall := localContactBall tau2762 center2762
def work2762 : RoundedTauEval :=
  evalTau precision tau2762 contact2762 logTwoBall

theorem center_sq2762 : (center2762.re : ℝ)^2 +
    (center2762.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2762]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2762 : work2762.theta.ok = true ∧
    work2762.jac.invOK = true ∧ acceptsUnitSq work2762.out = true := by decide +kernel

def cell2762 : CellCertificate where
  tauBall := tau2762
  contactCenter := center2762
  contactBall := contact2762
  work := work2762
  center_sq := center_sq2762
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2762.1
  jac_ok := checks2762.2.1
  accepted := checks2762.2.2

def tau2763 : RatBall :=
  ⟨⟨-51/640, -241/640⟩, 3/1280⟩
def center2763 : GaussianRat :=
  ⟨-16120741/250000000, -34094071/125000000⟩
def contact2763 : RatBall := localContactBall tau2763 center2763
def work2763 : RoundedTauEval :=
  evalTau precision tau2763 contact2763 logTwoBall

theorem center_sq2763 : (center2763.re : ℝ)^2 +
    (center2763.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2763]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2763 : work2763.theta.ok = true ∧
    work2763.jac.invOK = true ∧ acceptsUnitSq work2763.out = true := by decide +kernel

def cell2763 : CellCertificate where
  tauBall := tau2763
  contactCenter := center2763
  contactBall := contact2763
  work := work2763
  center_sq := center_sq2763
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2763.1
  jac_ok := checks2763.2.1
  accepted := checks2763.2.2

def tau2764 : RatBall :=
  ⟨⟨-49/640, -241/640⟩, 3/1280⟩
def center2764 : GaussianRat :=
  ⟨-12394897/200000000, -272930361/1000000000⟩
def contact2764 : RatBall := localContactBall tau2764 center2764
def work2764 : RoundedTauEval :=
  evalTau precision tau2764 contact2764 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345


