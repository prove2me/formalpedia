-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0262
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0262
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:21:59.68105+00:00
-- url     : https://prove2.me/theorems/a0deb37b-f8b3-4e49-a4e0-c9726a8ca364
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0262.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0262_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2101 : (center2101.re : ℝ)^2 +
    (center2101.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2101]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2101 : work2101.theta.ok = true ∧
    work2101.jac.invOK = true ∧ acceptsUnitSq work2101.out = true := by decide +kernel

def cell2101 : CellCertificate where
  tauBall := tau2101
  contactCenter := center2101
  contactBall := contact2101
  work := work2101
  center_sq := center_sq2101
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2101.1
  jac_ok := checks2101.2.1
  accepted := checks2101.2.2

def tau2102 : RatBall :=
  ⟨⟨-37/320, 21/64⟩, 3/640⟩
def center2102 : GaussianRat :=
  ⟨-89536891/1000000000, 116308561/500000000⟩
def contact2102 : RatBall := localContactBall tau2102 center2102
def work2102 : RoundedTauEval :=
  evalTau precision tau2102 contact2102 logTwoBall

theorem center_sq2102 : (center2102.re : ℝ)^2 +
    (center2102.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2102]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2102 : work2102.theta.ok = true ∧
    work2102.jac.invOK = true ∧ acceptsUnitSq work2102.out = true := by decide +kernel

def cell2102 : CellCertificate where
  tauBall := tau2102
  contactCenter := center2102
  contactBall := contact2102
  work := work2102
  center_sq := center_sq2102
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2102.1
  jac_ok := checks2102.2.1
  accepted := checks2102.2.2

def tau2103 : RatBall :=
  ⟨⟨-39/320, 107/320⟩, 3/640⟩
def center2103 : GaussianRat :=
  ⟨-23684951/250000000, 1184781/5000000⟩
def contact2103 : RatBall := localContactBall tau2103 center2103
def work2103 : RoundedTauEval :=
  evalTau precision tau2103 contact2103 logTwoBall

theorem center_sq2103 : (center2103.re : ℝ)^2 +
    (center2103.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2103]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2103 : work2103.theta.ok = true ∧
    work2103.jac.invOK = true ∧ acceptsUnitSq work2103.out = true := by decide +kernel

def cell2103 : CellCertificate where
  tauBall := tau2103
  contactCenter := center2103
  contactBall := contact2103
  work := work2103
  center_sq := center_sq2103
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2103.1
  jac_ok := checks2103.2.1
  accepted := checks2103.2.2

def cells : List CellCertificate := [cell2096, cell2097, cell2098, cell2099, cell2100, cell2101, cell2102, cell2103]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262


