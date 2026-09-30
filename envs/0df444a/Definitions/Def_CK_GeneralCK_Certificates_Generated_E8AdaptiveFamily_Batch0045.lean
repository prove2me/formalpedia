-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0045
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0045
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:58:46.026865+00:00
-- url     : https://prove2.me/theorems/23e1c5e1-0d17-47c9-86fb-e4bec6ca2cde
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0045.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0045_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0366 : work0366.theta.ok = true ∧
    work0366.jac.invOK = true ∧ acceptsUnitSq work0366.out = true := by decide +kernel

def cell0366 : CellCertificate where
  tauBall := tau0366
  contactCenter := center0366
  contactBall := contact0366
  work := work0366
  center_sq := center_sq0366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0366.1
  jac_ok := checks0366.2.1
  accepted := checks0366.2.2

def tau0367 : RatBall :=
  ⟨⟨-43/160, -37/160⟩, 3/320⟩
def center0367 : GaussianRat :=
  ⟨-191209303/1000000000, -1887097/12500000⟩
def contact0367 : RatBall := localContactBall tau0367 center0367
def work0367 : RoundedTauEval :=
  evalTau precision tau0367 contact0367 logTwoBall

theorem center_sq0367 : (center0367.re : ℝ)^2 +
    (center0367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0367 : work0367.theta.ok = true ∧
    work0367.jac.invOK = true ∧ acceptsUnitSq work0367.out = true := by decide +kernel

def cell0367 : CellCertificate where
  tauBall := tau0367
  contactCenter := center0367
  contactBall := contact0367
  work := work0367
  center_sq := center_sq0367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0367.1
  jac_ok := checks0367.2.1
  accepted := checks0367.2.2

def cells : List CellCertificate := [cell0360, cell0361, cell0362, cell0363, cell0364, cell0365, cell0366, cell0367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045


