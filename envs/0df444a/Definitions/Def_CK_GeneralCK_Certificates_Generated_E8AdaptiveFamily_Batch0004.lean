-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0004
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0004
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:08:12.938885+00:00
-- url     : https://prove2.me/theorems/2a7f2cae-dc96-447a-8966-5051966fa434
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0004.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0004_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0038 : RoundedTauEval :=
  evalTau precision tau0038 contact0038 logTwoBall

theorem center_sq0038 : (center0038.re : ℝ)^2 +
    (center0038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0038 : work0038.theta.ok = true ∧
    work0038.jac.invOK = true ∧ acceptsUnitSq work0038.out = true := by decide +kernel

def cell0038 : CellCertificate where
  tauBall := tau0038
  contactCenter := center0038
  contactBall := contact0038
  work := work0038
  center_sq := center_sq0038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0038.1
  jac_ok := checks0038.2.1
  accepted := checks0038.2.2

def tau0039 : RatBall :=
  ⟨⟨1/40, 1/40⟩, 3/80⟩
def center0039 : GaussianRat :=
  ⟨17336181/1000000000, 17321167/1000000000⟩
def contact0039 : RatBall := localContactBall tau0039 center0039
def work0039 : RoundedTauEval :=
  evalTau precision tau0039 contact0039 logTwoBall

theorem center_sq0039 : (center0039.re : ℝ)^2 +
    (center0039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0039 : work0039.theta.ok = true ∧
    work0039.jac.invOK = true ∧ acceptsUnitSq work0039.out = true := by decide +kernel

def cell0039 : CellCertificate where
  tauBall := tau0039
  contactCenter := center0039
  contactBall := contact0039
  work := work0039
  center_sq := center_sq0039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0039.1
  jac_ok := checks0039.2.1
  accepted := checks0039.2.2

def cells : List CellCertificate := [cell0032, cell0033, cell0034, cell0035, cell0036, cell0037, cell0038, cell0039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004


