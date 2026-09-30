-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:41.955666+00:00
-- url     : https://prove2.me/theorems/86f54b71-c9ff-4123-bc9c-a5df42ff9b1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0033.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0270 : (center0270.re : ℝ)^2 +
    (center0270.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0270]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0270 : work0270.theta.ok = true ∧
    work0270.jac.invOK = true ∧ acceptsUnitSq work0270.out = true := by decide +kernel

def cell0270 : CellCertificate where
  tauBall := tau0270
  contactCenter := center0270
  contactBall := contact0270
  work := work0270
  center_sq := center_sq0270
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0270.1
  jac_ok := checks0270.2.1
  accepted := checks0270.2.2

def tau0271 : RatBall :=
  ⟨⟨1/16, 13/80⟩, 3/160⟩
def center0271 : GaussianRat :=
  ⟨44475471/1000000000, 14150393/125000000⟩
def contact0271 : RatBall := localContactBall tau0271 center0271
def work0271 : RoundedTauEval :=
  evalTau precision tau0271 contact0271 logTwoBall

theorem center_sq0271 : (center0271.re : ℝ)^2 +
    (center0271.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0271]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0271 : work0271.theta.ok = true ∧
    work0271.jac.invOK = true ∧ acceptsUnitSq work0271.out = true := by decide +kernel

def cell0271 : CellCertificate where
  tauBall := tau0271
  contactCenter := center0271
  contactBall := contact0271
  work := work0271
  center_sq := center_sq0271
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0271.1
  jac_ok := checks0271.2.1
  accepted := checks0271.2.2

def cells : List CellCertificate := [cell0264, cell0265, cell0266, cell0267, cell0268, cell0269, cell0270, cell0271]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033


