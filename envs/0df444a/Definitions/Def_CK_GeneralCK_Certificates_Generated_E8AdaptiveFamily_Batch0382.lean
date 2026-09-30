-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0382
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0382
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:05:03.638394+00:00
-- url     : https://prove2.me/theorems/e0693b53-efc4-4dcb-bf1a-f1732bdbd914
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0382.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0382_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3062 : GaussianRat :=
  ⟨89415553/1000000000, -270605413/1000000000⟩
def contact3062 : RatBall := localContactBall tau3062 center3062
def work3062 : RoundedTauEval :=
  evalTau precision tau3062 contact3062 logTwoBall

theorem center_sq3062 : (center3062.re : ℝ)^2 +
    (center3062.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3062]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3062 : work3062.theta.ok = true ∧
    work3062.jac.invOK = true ∧ acceptsUnitSq work3062.out = true := by decide +kernel

def cell3062 : CellCertificate where
  tauBall := tau3062
  contactCenter := center3062
  contactBall := contact3062
  work := work3062
  center_sq := center_sq3062
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3062.1
  jac_ok := checks3062.2.1
  accepted := checks3062.2.2

def tau3063 : RatBall :=
  ⟨⟨73/640, -49/128⟩, 3/1280⟩
def center3063 : GaussianRat :=
  ⟨92406637/1000000000, -275316291/1000000000⟩
def contact3063 : RatBall := localContactBall tau3063 center3063
def work3063 : RoundedTauEval :=
  evalTau precision tau3063 contact3063 logTwoBall

theorem center_sq3063 : (center3063.re : ℝ)^2 +
    (center3063.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3063]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3063 : work3063.theta.ok = true ∧
    work3063.jac.invOK = true ∧ acceptsUnitSq work3063.out = true := by decide +kernel

def cell3063 : CellCertificate where
  tauBall := tau3063
  contactCenter := center3063
  contactBall := contact3063
  work := work3063
  center_sq := center_sq3063
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3063.1
  jac_ok := checks3063.2.1
  accepted := checks3063.2.2

def cells : List CellCertificate := [cell3056, cell3057, cell3058, cell3059, cell3060, cell3061, cell3062, cell3063]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382


