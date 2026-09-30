-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0204
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0204
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:12:24.005451+00:00
-- url     : https://prove2.me/theorems/608dff71-c77d-4d5d-82b8-cf3bba554002
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0204.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0204_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1638 : RatBall :=
  ⟨⟨39/320, -23/64⟩, 3/640⟩
def center1638 : GaussianRat :=
  ⟨773093/8000000, -128116201/500000000⟩
def contact1638 : RatBall := localContactBall tau1638 center1638
def work1638 : RoundedTauEval :=
  evalTau precision tau1638 contact1638 logTwoBall

theorem center_sq1638 : (center1638.re : ℝ)^2 +
    (center1638.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1638]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1638 : work1638.theta.ok = true ∧
    work1638.jac.invOK = true ∧ acceptsUnitSq work1638.out = true := by decide +kernel

def cell1638 : CellCertificate where
  tauBall := tau1638
  contactCenter := center1638
  contactBall := contact1638
  work := work1638
  center_sq := center_sq1638
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1638.1
  jac_ok := checks1638.2.1
  accepted := checks1638.2.2

def tau1639 : RatBall :=
  ⟨⟨37/320, -113/320⟩, 3/640⟩
def center1639 : GaussianRat :=
  ⟨45647467/500000000, -62963873/250000000⟩
def contact1639 : RatBall := localContactBall tau1639 center1639
def work1639 : RoundedTauEval :=
  evalTau precision tau1639 contact1639 logTwoBall

theorem center_sq1639 : (center1639.re : ℝ)^2 +
    (center1639.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1639]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1639 : work1639.theta.ok = true ∧
    work1639.jac.invOK = true ∧ acceptsUnitSq work1639.out = true := by decide +kernel

def cell1639 : CellCertificate where
  tauBall := tau1639
  contactCenter := center1639
  contactBall := contact1639
  work := work1639
  center_sq := center_sq1639
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1639.1
  jac_ok := checks1639.2.1
  accepted := checks1639.2.2

def cells : List CellCertificate := [cell1632, cell1633, cell1634, cell1635, cell1636, cell1637, cell1638, cell1639]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204


