-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0005
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:24:11.990299+00:00
-- url     : https://prove2.me/theorems/e8d714a9-0846-44ec-9644-0ef9a1d16449
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0005.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0005_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0046 : RatBall :=
  ⟨⟨7/40, 3/40⟩, 3/80⟩
def center0046 : GaussianRat :=
  ⟨7544217/62500000, 12616221/250000000⟩
def contact0046 : RatBall := localContactBall tau0046 center0046
def work0046 : RoundedTauEval :=
  evalTau precision tau0046 contact0046 logTwoBall

theorem center_sq0046 : (center0046.re : ℝ)^2 +
    (center0046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0046 : work0046.theta.ok = true ∧
    work0046.jac.invOK = true ∧ acceptsUnitSq work0046.out = true := by decide +kernel

def cell0046 : CellCertificate where
  tauBall := tau0046
  contactCenter := center0046
  contactBall := contact0046
  work := work0046
  center_sq := center_sq0046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0046.1
  jac_ok := checks0046.2.1
  accepted := checks0046.2.2

def tau0047 : RatBall :=
  ⟨⟨1/40, 1/8⟩, 3/80⟩
def center0047 : GaussianRat :=
  ⟨17610637/1000000000, 8705903/100000000⟩
def contact0047 : RatBall := localContactBall tau0047 center0047
def work0047 : RoundedTauEval :=
  evalTau precision tau0047 contact0047 logTwoBall

theorem center_sq0047 : (center0047.re : ℝ)^2 +
    (center0047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0047 : work0047.theta.ok = true ∧
    work0047.jac.invOK = true ∧ acceptsUnitSq work0047.out = true := by decide +kernel

def cell0047 : CellCertificate where
  tauBall := tau0047
  contactCenter := center0047
  contactBall := contact0047
  work := work0047
  center_sq := center_sq0047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0047.1
  jac_ok := checks0047.2.1
  accepted := checks0047.2.2

def cells : List CellCertificate := [cell0040, cell0041, cell0042, cell0043, cell0044, cell0045, cell0046, cell0047]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0005


