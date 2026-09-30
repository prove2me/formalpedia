-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0460
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0460
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:22:03.431366+00:00
-- url     : https://prove2.me/theorems/c0f49ad6-3948-4e04-ad6f-42c09f3dd8d8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0460.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0460_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3686 : GaussianRat :=
  ⟨16077783/200000000, 281560103/1000000000⟩
def contact3686 : RatBall := localContactBall tau3686 center3686
def work3686 : RoundedTauEval :=
  evalTau precision tau3686 contact3686 logTwoBall

theorem center_sq3686 : (center3686.re : ℝ)^2 +
    (center3686.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3686]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3686 : work3686.theta.ok = true ∧
    work3686.jac.invOK = true ∧ acceptsUnitSq work3686.out = true := by decide +kernel

def cell3686 : CellCertificate where
  tauBall := tau3686
  contactCenter := center3686
  contactBall := contact3686
  work := work3686
  center_sq := center_sq3686
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3686.1
  jac_ok := checks3686.2.1
  accepted := checks3686.2.2

def tau3687 : RatBall :=
  ⟨⟨121/640, 221/640⟩, 3/1280⟩
def center3687 : GaussianRat :=
  ⟨146422507/1000000000, 9563167/40000000⟩
def contact3687 : RatBall := localContactBall tau3687 center3687
def work3687 : RoundedTauEval :=
  evalTau precision tau3687 contact3687 logTwoBall

theorem center_sq3687 : (center3687.re : ℝ)^2 +
    (center3687.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3687]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3687 : work3687.theta.ok = true ∧
    work3687.jac.invOK = true ∧ acceptsUnitSq work3687.out = true := by decide +kernel

def cell3687 : CellCertificate where
  tauBall := tau3687
  contactCenter := center3687
  contactBall := contact3687
  work := work3687
  center_sq := center_sq3687
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3687.1
  jac_ok := checks3687.2.1
  accepted := checks3687.2.2

def cells : List CellCertificate := [cell3680, cell3681, cell3682, cell3683, cell3684, cell3685, cell3686, cell3687]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460


