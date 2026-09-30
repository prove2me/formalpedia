-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:02:32.883159+00:00
-- url     : https://prove2.me/theorems/03d84c87-e5d6-4303-828f-c6a908fb896f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0243 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1948 : CellCertificate where
  tauBall := tau1948
  contactCenter := center1948
  contactBall := contact1948
  work := work1948
  center_sq := center_sq1948
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1948.1
  jac_ok := checks1948.2.1
  accepted := checks1948.2.2

def tau1949 : RatBall :=
  ⟨⟨-83/320, 91/320⟩, 3/640⟩
def center1949 : GaussianRat :=
  ⟨-37988073/200000000, 37573667/200000000⟩
def contact1949 : RatBall := localContactBall tau1949 center1949
def work1949 : RoundedTauEval :=
  evalTau precision tau1949 contact1949 logTwoBall

theorem center_sq1949 : (center1949.re : ℝ)^2 +
    (center1949.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1949]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1949 : work1949.theta.ok = true ∧
    work1949.jac.invOK = true ∧ acceptsUnitSq work1949.out = true := by decide +kernel

def cell1949 : CellCertificate where
  tauBall := tau1949
  contactCenter := center1949
  contactBall := contact1949
  work := work1949
  center_sq := center_sq1949
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1949.1
  jac_ok := checks1949.2.1
  accepted := checks1949.2.2

def tau1950 : RatBall :=
  ⟨⟨-81/320, 91/320⟩, 3/640⟩
def center1950 : GaussianRat :=
  ⟨-23204849/125000000, 94265223/500000000⟩
def contact1950 : RatBall := localContactBall tau1950 center1950
def work1950 : RoundedTauEval :=
  evalTau precision tau1950 contact1950 logTwoBall

theorem center_sq1950 : (center1950.re : ℝ)^2 +
    (center1950.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1950]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1950 : work1950.theta.ok = true ∧
    work1950.jac.invOK = true ∧ acceptsUnitSq work1950.out = true := by decide +kernel

def cell1950 : CellCertificate where
  tauBall := tau1950
  contactCenter := center1950
  contactBall := contact1950
  work := work1950
  center_sq := center_sq1950
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1950.1
  jac_ok := checks1950.2.1
  accepted := checks1950.2.2

def tau1951 : RatBall :=
  ⟨⟨-87/320, 93/320⟩, 3/640⟩
def center1951 : GaussianRat :=
  ⟨-2489819/12500000, 47692707/250000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243


