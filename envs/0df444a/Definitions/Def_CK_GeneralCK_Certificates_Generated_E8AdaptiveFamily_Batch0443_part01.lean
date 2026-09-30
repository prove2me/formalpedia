-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:09.227468+00:00
-- url     : https://prove2.me/theorems/9a8c2641-1d67-40ae-9efd-35de090eca31
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0443 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3546 : GaussianRat :=
  ⟨8373251/500000000, 287713133/1000000000⟩
def contact3546 : RatBall := localContactBall tau3546 center3546
def work3546 : RoundedTauEval :=
  evalTau precision tau3546 contact3546 logTwoBall

theorem center_sq3546 : (center3546.re : ℝ)^2 +
    (center3546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3546 : work3546.theta.ok = true ∧
    work3546.jac.invOK = true ∧ acceptsUnitSq work3546.out = true := by decide +kernel

def cell3546 : CellCertificate where
  tauBall := tau3546
  contactCenter := center3546
  contactBall := contact3546
  work := work3546
  center_sq := center_sq3546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3546.1
  jac_ok := checks3546.2.1
  accepted := checks3546.2.2

def tau3547 : RatBall :=
  ⟨⟨3/128, 251/640⟩, 3/1280⟩
def center3547 : GaussianRat :=
  ⟨3864199/200000000, 57531759/200000000⟩
def contact3547 : RatBall := localContactBall tau3547 center3547
def work3547 : RoundedTauEval :=
  evalTau precision tau3547 contact3547 logTwoBall

theorem center_sq3547 : (center3547.re : ℝ)^2 +
    (center3547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3547 : work3547.theta.ok = true ∧
    work3547.jac.invOK = true ∧ acceptsUnitSq work3547.out = true := by decide +kernel

def cell3547 : CellCertificate where
  tauBall := tau3547
  contactCenter := center3547
  contactBall := contact3547
  work := work3547
  center_sq := center_sq3547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3547.1
  jac_ok := checks3547.2.1
  accepted := checks3547.2.2

def tau3548 : RatBall :=
  ⟨⟨9/640, 253/640⟩, 3/1280⟩
def center3548 : GaussianRat :=
  ⟨5815363/500000000, 145189259/500000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443


