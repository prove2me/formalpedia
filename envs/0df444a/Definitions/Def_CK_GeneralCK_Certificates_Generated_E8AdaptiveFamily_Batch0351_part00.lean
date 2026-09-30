-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:06:34.186112+00:00
-- url     : https://prove2.me/theorems/1993301e-74ac-4df3-ba3f-061517d2a0c9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0351 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2808 : RatBall :=
  ⟨⟨-31/640, -51/128⟩, 3/1280⟩
def center2808 : GaussianRat :=
  ⟨-20060649/500000000, -146045357/500000000⟩
def contact2808 : RatBall := localContactBall tau2808 center2808
def work2808 : RoundedTauEval :=
  evalTau precision tau2808 contact2808 logTwoBall

theorem center_sq2808 : (center2808.re : ℝ)^2 +
    (center2808.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2808]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2808 : work2808.theta.ok = true ∧
    work2808.jac.invOK = true ∧ acceptsUnitSq work2808.out = true := by decide +kernel

def cell2808 : CellCertificate where
  tauBall := tau2808
  contactCenter := center2808
  contactBall := contact2808
  work := work2808
  center_sq := center_sq2808
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2808.1
  jac_ok := checks2808.2.1
  accepted := checks2808.2.2

def tau2809 : RatBall :=
  ⟨⟨-29/640, -51/128⟩, 3/1280⟩
def center2809 : GaussianRat :=
  ⟨-2346303/62500000, -292209741/1000000000⟩
def contact2809 : RatBall := localContactBall tau2809 center2809
def work2809 : RoundedTauEval :=
  evalTau precision tau2809 contact2809 logTwoBall

theorem center_sq2809 : (center2809.re : ℝ)^2 +
    (center2809.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2809]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2809 : work2809.theta.ok = true ∧
    work2809.jac.invOK = true ∧ acceptsUnitSq work2809.out = true := by decide +kernel

def cell2809 : CellCertificate where
  tauBall := tau2809
  contactCenter := center2809
  contactBall := contact2809
  work := work2809
  center_sq := center_sq2809
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2809.1
  jac_ok := checks2809.2.1
  accepted := checks2809.2.2

def tau2810 : RatBall :=
  ⟨⟨-31/640, -253/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351


