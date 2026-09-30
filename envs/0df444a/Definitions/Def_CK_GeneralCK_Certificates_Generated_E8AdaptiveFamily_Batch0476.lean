-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0476
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0476
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:24:49.34712+00:00
-- url     : https://prove2.me/theorems/27afb0d4-29fb-4744-ba74-1229d3ef42db
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0476.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0476_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3814 : work3814.theta.ok = true ∧
    work3814.jac.invOK = true ∧ acceptsUnitSq work3814.out = true := by decide +kernel

def cell3814 : CellCertificate where
  tauBall := tau3814
  contactCenter := center3814
  contactBall := contact3814
  work := work3814
  center_sq := center_sq3814
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3814.1
  jac_ok := checks3814.2.1
  accepted := checks3814.2.2

def tau3815 : RatBall :=
  ⟨⟨23/128, 45/128⟩, 3/1280⟩
def center3815 : GaussianRat :=
  ⟨5604287/40000000, 122385171/500000000⟩
def contact3815 : RatBall := localContactBall tau3815 center3815
def work3815 : RoundedTauEval :=
  evalTau precision tau3815 contact3815 logTwoBall

theorem center_sq3815 : (center3815.re : ℝ)^2 +
    (center3815.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3815]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3815 : work3815.theta.ok = true ∧
    work3815.jac.invOK = true ∧ acceptsUnitSq work3815.out = true := by decide +kernel

def cell3815 : CellCertificate where
  tauBall := tau3815
  contactCenter := center3815
  contactBall := contact3815
  work := work3815
  center_sq := center_sq3815
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3815.1
  jac_ok := checks3815.2.1
  accepted := checks3815.2.2

def cells : List CellCertificate := [cell3808, cell3809, cell3810, cell3811, cell3812, cell3813, cell3814, cell3815]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476


