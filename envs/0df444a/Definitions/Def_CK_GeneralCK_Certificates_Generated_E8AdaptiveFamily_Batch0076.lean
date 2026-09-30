-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0076
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0076
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:18:09.351754+00:00
-- url     : https://prove2.me/theorems/b960fa12-743a-4a07-ab90-27ed0f6432ca
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0076.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0076_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0614 : work0614.theta.ok = true ∧
    work0614.jac.invOK = true ∧ acceptsUnitSq work0614.out = true := by decide +kernel

def cell0614 : CellCertificate where
  tauBall := tau0614
  contactCenter := center0614
  contactBall := contact0614
  work := work0614
  center_sq := center_sq0614
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0614.1
  jac_ok := checks0614.2.1
  accepted := checks0614.2.2

def tau0615 : RatBall :=
  ⟨⟨19/160, -43/160⟩, 3/320⟩
def center0615 : GaussianRat :=
  ⟨88375401/1000000000, -188036739/1000000000⟩
def contact0615 : RatBall := localContactBall tau0615 center0615
def work0615 : RoundedTauEval :=
  evalTau precision tau0615 contact0615 logTwoBall

theorem center_sq0615 : (center0615.re : ℝ)^2 +
    (center0615.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0615]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0615 : work0615.theta.ok = true ∧
    work0615.jac.invOK = true ∧ acceptsUnitSq work0615.out = true := by decide +kernel

def cell0615 : CellCertificate where
  tauBall := tau0615
  contactCenter := center0615
  contactBall := contact0615
  work := work0615
  center_sq := center_sq0615
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0615.1
  jac_ok := checks0615.2.1
  accepted := checks0615.2.2

def cells : List CellCertificate := [cell0608, cell0609, cell0610, cell0611, cell0612, cell0613, cell0614, cell0615]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076


