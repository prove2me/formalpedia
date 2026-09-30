-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:31.040168+00:00
-- url     : https://prove2.me/theorems/9e118ac7-a915-4e56-bd35-110e29450ee7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0236 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1892 : CellCertificate where
  tauBall := tau1892
  contactCenter := center1892
  contactBall := contact1892
  work := work1892
  center_sq := center_sq1892
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1892.1
  jac_ok := checks1892.2.1
  accepted := checks1892.2.2

def tau1893 : RatBall :=
  ⟨⟨-103/320, 73/320⟩, 3/640⟩
def center1893 : GaussianRat :=
  ⟨-5645929/25000000, 9009977/62500000⟩
def contact1893 : RatBall := localContactBall tau1893 center1893
def work1893 : RoundedTauEval :=
  evalTau precision tau1893 contact1893 logTwoBall

theorem center_sq1893 : (center1893.re : ℝ)^2 +
    (center1893.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1893]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1893 : work1893.theta.ok = true ∧
    work1893.jac.invOK = true ∧ acceptsUnitSq work1893.out = true := by decide +kernel

def cell1893 : CellCertificate where
  tauBall := tau1893
  contactCenter := center1893
  contactBall := contact1893
  work := work1893
  center_sq := center_sq1893
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1893.1
  jac_ok := checks1893.2.1
  accepted := checks1893.2.2

def tau1894 : RatBall :=
  ⟨⟨-101/320, 73/320⟩, 3/640⟩
def center1894 : GaussianRat :=
  ⟨-44359939/200000000, 72370703/500000000⟩
def contact1894 : RatBall := localContactBall tau1894 center1894
def work1894 : RoundedTauEval :=
  evalTau precision tau1894 contact1894 logTwoBall

theorem center_sq1894 : (center1894.re : ℝ)^2 +
    (center1894.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1894]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1894 : work1894.theta.ok = true ∧
    work1894.jac.invOK = true ∧ acceptsUnitSq work1894.out = true := by decide +kernel

def cell1894 : CellCertificate where
  tauBall := tau1894
  contactCenter := center1894
  contactBall := contact1894
  work := work1894
  center_sq := center_sq1894
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1894.1
  jac_ok := checks1894.2.1
  accepted := checks1894.2.2

def tau1895 : RatBall :=
  ⟨⟨-103/320, 15/64⟩, 3/640⟩
def center1895 : GaussianRat :=
  ⟨-14151969/62500000, 148191091/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236


