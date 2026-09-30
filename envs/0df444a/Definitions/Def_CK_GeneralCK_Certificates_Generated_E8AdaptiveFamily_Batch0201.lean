-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0201
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0201
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:16:31.01599+00:00
-- url     : https://prove2.me/theorems/bffe7aff-5211-4c6b-ad65-37b062f9cdfd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0201.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0201_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1614 : RatBall :=
  ⟨⟨31/320, -23/64⟩, 3/640⟩
def center1614 : GaussianRat :=
  ⟨77076663/1000000000, -258044723/1000000000⟩
def contact1614 : RatBall := localContactBall tau1614 center1614
def work1614 : RoundedTauEval :=
  evalTau precision tau1614 contact1614 logTwoBall

theorem center_sq1614 : (center1614.re : ℝ)^2 +
    (center1614.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1614]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1614 : work1614.theta.ok = true ∧
    work1614.jac.invOK = true ∧ acceptsUnitSq work1614.out = true := by decide +kernel

def cell1614 : CellCertificate where
  tauBall := tau1614
  contactCenter := center1614
  contactBall := contact1614
  work := work1614
  center_sq := center_sq1614
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1614.1
  jac_ok := checks1614.2.1
  accepted := checks1614.2.2

def tau1615 : RatBall :=
  ⟨⟨29/320, -113/320⟩, 3/640⟩
def center1615 : GaussianRat :=
  ⟨1794563/25000000, -253524459/1000000000⟩
def contact1615 : RatBall := localContactBall tau1615 center1615
def work1615 : RoundedTauEval :=
  evalTau precision tau1615 contact1615 logTwoBall

theorem center_sq1615 : (center1615.re : ℝ)^2 +
    (center1615.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1615]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1615 : work1615.theta.ok = true ∧
    work1615.jac.invOK = true ∧ acceptsUnitSq work1615.out = true := by decide +kernel

def cell1615 : CellCertificate where
  tauBall := tau1615
  contactCenter := center1615
  contactBall := contact1615
  work := work1615
  center_sq := center_sq1615
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1615.1
  jac_ok := checks1615.2.1
  accepted := checks1615.2.2

def cells : List CellCertificate := [cell1608, cell1609, cell1610, cell1611, cell1612, cell1613, cell1614, cell1615]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201


