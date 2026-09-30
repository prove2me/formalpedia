-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:38.035835+00:00
-- url     : https://prove2.me/theorems/17852667-4f33-4933-a33d-e5b0e282d5d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0236 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1888 : RatBall :=
  ⟨⟨-21/64, 69/320⟩, 3/640⟩
def center1888 : GaussianRat :=
  ⟨-57177633/250000000, 13556449/100000000⟩
def contact1888 : RatBall := localContactBall tau1888 center1888
def work1888 : RoundedTauEval :=
  evalTau precision tau1888 contact1888 logTwoBall

theorem center_sq1888 : (center1888.re : ℝ)^2 +
    (center1888.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1888]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1888 : work1888.theta.ok = true ∧
    work1888.jac.invOK = true ∧ acceptsUnitSq work1888.out = true := by decide +kernel

def cell1888 : CellCertificate where
  tauBall := tau1888
  contactCenter := center1888
  contactBall := contact1888
  work := work1888
  center_sq := center_sq1888
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1888.1
  jac_ok := checks1888.2.1
  accepted := checks1888.2.2

def tau1889 : RatBall :=
  ⟨⟨-107/320, 71/320⟩, 3/640⟩
def center1889 : GaussianRat :=
  ⟨-58317051/250000000, 34747303/250000000⟩
def contact1889 : RatBall := localContactBall tau1889 center1889
def work1889 : RoundedTauEval :=
  evalTau precision tau1889 contact1889 logTwoBall

theorem center_sq1889 : (center1889.re : ℝ)^2 +
    (center1889.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1889]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1889 : work1889.theta.ok = true ∧
    work1889.jac.invOK = true ∧ acceptsUnitSq work1889.out = true := by decide +kernel

def cell1889 : CellCertificate where
  tauBall := tau1889
  contactCenter := center1889
  contactBall := contact1889
  work := work1889
  center_sq := center_sq1889
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1889.1
  jac_ok := checks1889.2.1
  accepted := checks1889.2.2

def tau1890 : RatBall :=
  ⟨⟨-21/64, 71/320⟩, 3/640⟩
def center1890 : GaussianRat :=
  ⟨-45854809/200000000, 139564933/1000000000⟩
def contact1890 : RatBall := localContactBall tau1890 center1890

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236


