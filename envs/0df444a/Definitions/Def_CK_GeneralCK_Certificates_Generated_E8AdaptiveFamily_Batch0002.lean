-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0002
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0002
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:09:33.29193+00:00
-- url     : https://prove2.me/theorems/558c9a57-e35a-4cf6-9cca-9e5339d4607c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0002.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0002_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0022 : (center0022.re : ℝ)^2 +
    (center0022.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0022]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0022 : work0022.theta.ok = true ∧
    work0022.jac.invOK = true ∧ acceptsUnitSq work0022.out = true := by decide +kernel

def cell0022 : CellCertificate where
  tauBall := tau0022
  contactCenter := center0022
  contactBall := contact0022
  work := work0022
  center_sq := center_sq0022
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0022.1
  jac_ok := checks0022.2.1
  accepted := checks0022.2.2

def tau0023 : RatBall :=
  ⟨⟨1/8, -1/40⟩, 3/80⟩
def center0023 : GaussianRat :=
  ⟨8623323/100000000, -17054997/1000000000⟩
def contact0023 : RatBall := localContactBall tau0023 center0023
def work0023 : RoundedTauEval :=
  evalTau precision tau0023 contact0023 logTwoBall

theorem center_sq0023 : (center0023.re : ℝ)^2 +
    (center0023.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0023]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0023 : work0023.theta.ok = true ∧
    work0023.jac.invOK = true ∧ acceptsUnitSq work0023.out = true := by decide +kernel

def cell0023 : CellCertificate where
  tauBall := tau0023
  contactCenter := center0023
  contactBall := contact0023
  work := work0023
  center_sq := center_sq0023
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0023.1
  jac_ok := checks0023.2.1
  accepted := checks0023.2.2

def cells : List CellCertificate := [cell0016, cell0017, cell0018, cell0019, cell0020, cell0021, cell0022, cell0023]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002


