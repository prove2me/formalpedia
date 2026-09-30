-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:17:47.571094+00:00
-- url     : https://prove2.me/theorems/23ceeb87-a986-497b-a95d-835119a794dc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0008 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0064 : RatBall :=
  ⟨⟨-7/80, -19/80⟩, 3/160⟩
def center0064 : GaussianRat :=
  ⟨-32100469/500000000, -83247331/500000000⟩
def contact0064 : RatBall := localContactBall tau0064 center0064
def work0064 : RoundedTauEval :=
  evalTau precision tau0064 contact0064 logTwoBall

theorem center_sq0064 : (center0064.re : ℝ)^2 +
    (center0064.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0064]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0064 : work0064.theta.ok = true ∧
    work0064.jac.invOK = true ∧ acceptsUnitSq work0064.out = true := by decide +kernel

def cell0064 : CellCertificate where
  tauBall := tau0064
  contactCenter := center0064
  contactBall := contact0064
  work := work0064
  center_sq := center_sq0064
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0064.1
  jac_ok := checks0064.2.1
  accepted := checks0064.2.2

def tau0065 : RatBall :=
  ⟨⟨-1/16, -19/80⟩, 3/160⟩
def center0065 : GaussianRat :=
  ⟨-45935893/1000000000, -836037/5000000⟩
def contact0065 : RatBall := localContactBall tau0065 center0065
def work0065 : RoundedTauEval :=
  evalTau precision tau0065 contact0065 logTwoBall

theorem center_sq0065 : (center0065.re : ℝ)^2 +
    (center0065.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0065]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0065 : work0065.theta.ok = true ∧
    work0065.jac.invOK = true ∧ acceptsUnitSq work0065.out = true := by decide +kernel

def cell0065 : CellCertificate where
  tauBall := tau0065
  contactCenter := center0065
  contactBall := contact0065
  work := work0065
  center_sq := center_sq0065
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0065.1
  jac_ok := checks0065.2.1
  accepted := checks0065.2.2

def tau0066 : RatBall :=
  ⟨⟨-7/80, -17/80⟩, 3/160⟩
def center0066 : GaussianRat :=
  ⟨-31712973/500000000, -37096923/250000000⟩
def contact0066 : RatBall := localContactBall tau0066 center0066
def work0066 : RoundedTauEval :=
  evalTau precision tau0066 contact0066 logTwoBall

theorem center_sq0066 : (center0066.re : ℝ)^2 +
    (center0066.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0066]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0066 : work0066.theta.ok = true ∧
    work0066.jac.invOK = true ∧ acceptsUnitSq work0066.out = true := by decide +kernel

def cell0066 : CellCertificate where
  tauBall := tau0066
  contactCenter := center0066
  contactBall := contact0066
  work := work0066
  center_sq := center_sq0066
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0066.1
  jac_ok := checks0066.2.1
  accepted := checks0066.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008


