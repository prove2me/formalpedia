-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0071
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0071
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:22:31.759538+00:00
-- url     : https://prove2.me/theorems/05f40b4c-1e49-4f2a-bcad-781ca3b068c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0071.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0071_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0574 : CellCertificate where
  tauBall := tau0574
  contactCenter := center0574
  contactBall := contact0574
  work := work0574
  center_sq := center_sq0574
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0574.1
  jac_ok := checks0574.2.1
  accepted := checks0574.2.2

def tau0575 : RatBall :=
  ⟨⟨9/160, -11/32⟩, 3/320⟩
def center0575 : GaussianRat :=
  ⟨44352537/1000000000, -61948059/250000000⟩
def contact0575 : RatBall := localContactBall tau0575 center0575
def work0575 : RoundedTauEval :=
  evalTau precision tau0575 contact0575 logTwoBall

theorem center_sq0575 : (center0575.re : ℝ)^2 +
    (center0575.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0575 : work0575.theta.ok = true ∧
    work0575.jac.invOK = true ∧ acceptsUnitSq work0575.out = true := by decide +kernel

def cell0575 : CellCertificate where
  tauBall := tau0575
  contactCenter := center0575
  contactBall := contact0575
  work := work0575
  center_sq := center_sq0575
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0575.1
  jac_ok := checks0575.2.1
  accepted := checks0575.2.2

def cells : List CellCertificate := [cell0568, cell0569, cell0570, cell0571, cell0572, cell0573, cell0574, cell0575]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071


