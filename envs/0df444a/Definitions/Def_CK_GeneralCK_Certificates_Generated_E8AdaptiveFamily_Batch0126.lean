-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0126
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0126
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:45:54.23251+00:00
-- url     : https://prove2.me/theorems/1d626e7f-2ee4-41a6-923e-bd8e51114a37
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0126.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0126_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1014 : work1014.theta.ok = true ∧
    work1014.jac.invOK = true ∧ acceptsUnitSq work1014.out = true := by decide +kernel

def cell1014 : CellCertificate where
  tauBall := tau1014
  contactCenter := center1014
  contactBall := contact1014
  work := work1014
  center_sq := center_sq1014
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1014.1
  jac_ok := checks1014.2.1
  accepted := checks1014.2.2

def tau1015 : RatBall :=
  ⟨⟨47/160, 29/160⟩, 3/320⟩
def center1015 : GaussianRat :=
  ⟨25481847/125000000, 58047077/500000000⟩
def contact1015 : RatBall := localContactBall tau1015 center1015
def work1015 : RoundedTauEval :=
  evalTau precision tau1015 contact1015 logTwoBall

theorem center_sq1015 : (center1015.re : ℝ)^2 +
    (center1015.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1015]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1015 : work1015.theta.ok = true ∧
    work1015.jac.invOK = true ∧ acceptsUnitSq work1015.out = true := by decide +kernel

def cell1015 : CellCertificate where
  tauBall := tau1015
  contactCenter := center1015
  contactBall := contact1015
  work := work1015
  center_sq := center_sq1015
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1015.1
  jac_ok := checks1015.2.1
  accepted := checks1015.2.2

def cells : List CellCertificate := [cell1008, cell1009, cell1010, cell1011, cell1012, cell1013, cell1014, cell1015]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126


