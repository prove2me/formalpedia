-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:02:09.272018+00:00
-- url     : https://prove2.me/theorems/88948855-4312-4b0f-9452-38a9bd2850b0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0123.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0990 : RoundedTauEval :=
  evalTau precision tau0990 contact0990 logTwoBall

theorem center_sq0990 : (center0990.re : ℝ)^2 +
    (center0990.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0990]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0990 : work0990.theta.ok = true ∧
    work0990.jac.invOK = true ∧ acceptsUnitSq work0990.out = true := by decide +kernel

def cell0990 : CellCertificate where
  tauBall := tau0990
  contactCenter := center0990
  contactBall := contact0990
  work := work0990
  center_sq := center_sq0990
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0990.1
  jac_ok := checks0990.2.1
  accepted := checks0990.2.2

def tau0991 : RatBall :=
  ⟨⟨63/160, 9/160⟩, 3/320⟩
def center0991 : GaussianRat :=
  ⟨65046299/250000000, 6715607/200000000⟩
def contact0991 : RatBall := localContactBall tau0991 center0991
def work0991 : RoundedTauEval :=
  evalTau precision tau0991 contact0991 logTwoBall

theorem center_sq0991 : (center0991.re : ℝ)^2 +
    (center0991.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0991]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0991 : work0991.theta.ok = true ∧
    work0991.jac.invOK = true ∧ acceptsUnitSq work0991.out = true := by decide +kernel

def cell0991 : CellCertificate where
  tauBall := tau0991
  contactCenter := center0991
  contactBall := contact0991
  work := work0991
  center_sq := center_sq0991
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0991.1
  jac_ok := checks0991.2.1
  accepted := checks0991.2.2

def cells : List CellCertificate := [cell0984, cell0985, cell0986, cell0987, cell0988, cell0989, cell0990, cell0991]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123


