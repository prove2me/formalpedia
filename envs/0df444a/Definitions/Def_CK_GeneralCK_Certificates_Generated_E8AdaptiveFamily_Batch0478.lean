-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:00:03.219982+00:00
-- url     : https://prove2.me/theorems/22d200f3-f737-4c42-b2ef-0eb7cb1e0a95
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0478.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0478_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3830 : RatBall := localContactBall tau3830 center3830
def work3830 : RoundedTauEval :=
  evalTau precision tau3830 contact3830 logTwoBall

theorem center_sq3830 : (center3830.re : ℝ)^2 +
    (center3830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3830 : work3830.theta.ok = true ∧
    work3830.jac.invOK = true ∧ acceptsUnitSq work3830.out = true := by decide +kernel

def cell3830 : CellCertificate where
  tauBall := tau3830
  contactCenter := center3830
  contactBall := contact3830
  work := work3830
  center_sq := center_sq3830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3830.1
  jac_ok := checks3830.2.1
  accepted := checks3830.2.2

def tau3831 : RatBall :=
  ⟨⟨141/640, 43/128⟩, 3/1280⟩
def center3831 : GaussianRat :=
  ⟨84129393/500000000, 228617923/1000000000⟩
def contact3831 : RatBall := localContactBall tau3831 center3831
def work3831 : RoundedTauEval :=
  evalTau precision tau3831 contact3831 logTwoBall

theorem center_sq3831 : (center3831.re : ℝ)^2 +
    (center3831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3831 : work3831.theta.ok = true ∧
    work3831.jac.invOK = true ∧ acceptsUnitSq work3831.out = true := by decide +kernel

def cell3831 : CellCertificate where
  tauBall := tau3831
  contactCenter := center3831
  contactBall := contact3831
  work := work3831
  center_sq := center_sq3831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3831.1
  jac_ok := checks3831.2.1
  accepted := checks3831.2.2

def cells : List CellCertificate := [cell3824, cell3825, cell3826, cell3827, cell3828, cell3829, cell3830, cell3831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478


