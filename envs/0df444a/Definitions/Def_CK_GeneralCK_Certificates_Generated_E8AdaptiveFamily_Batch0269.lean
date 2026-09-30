-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0269
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0269
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:06:17.890425+00:00
-- url     : https://prove2.me/theorems/2101a0b7-52ba-416f-a02a-762a299332ee
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0269.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0269_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2158 : CellCertificate where
  tauBall := tau2158
  contactCenter := center2158
  contactBall := contact2158
  work := work2158
  center_sq := center_sq2158
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2158.1
  jac_ok := checks2158.2.1
  accepted := checks2158.2.2

def tau2159 : RatBall :=
  ⟨⟨-27/320, 117/320⟩, 3/640⟩
def center2159 : GaussianRat :=
  ⟨-844837/12500000, 131876019/500000000⟩
def contact2159 : RatBall := localContactBall tau2159 center2159
def work2159 : RoundedTauEval :=
  evalTau precision tau2159 contact2159 logTwoBall

theorem center_sq2159 : (center2159.re : ℝ)^2 +
    (center2159.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2159]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2159 : work2159.theta.ok = true ∧
    work2159.jac.invOK = true ∧ acceptsUnitSq work2159.out = true := by decide +kernel

def cell2159 : CellCertificate where
  tauBall := tau2159
  contactCenter := center2159
  contactBall := contact2159
  work := work2159
  center_sq := center_sq2159
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2159.1
  jac_ok := checks2159.2.1
  accepted := checks2159.2.2

def cells : List CellCertificate := [cell2152, cell2153, cell2154, cell2155, cell2156, cell2157, cell2158, cell2159]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269


