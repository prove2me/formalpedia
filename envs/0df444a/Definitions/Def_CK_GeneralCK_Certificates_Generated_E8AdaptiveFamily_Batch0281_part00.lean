-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0281_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:06:36.902405+00:00
-- url     : https://prove2.me/theorems/15585a8e-a055-4d71-a87b-be128e146c90
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281 (part 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0281 (part 1 of 5).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2248 : RatBall :=
  ⟨⟨9/320, 113/320⟩, 3/640⟩
def center2248 : GaussianRat :=
  ⟨22380501/1000000000, 127986203/500000000⟩
def contact2248 : RatBall := localContactBall tau2248 center2248
def work2248 : RoundedTauEval :=
  evalTau precision tau2248 contact2248 logTwoBall

theorem center_sq2248 : (center2248.re : ℝ)^2 +
    (center2248.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2248 : work2248.theta.ok = true ∧
    work2248.jac.invOK = true ∧ acceptsUnitSq work2248.out = true := by decide +kernel

def cell2248 : CellCertificate where
  tauBall := tau2248
  contactCenter := center2248
  contactBall := contact2248
  work := work2248
  center_sq := center_sq2248
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2248.1
  jac_ok := checks2248.2.1
  accepted := checks2248.2.2

def tau2249 : RatBall :=
  ⟨⟨11/320, 113/320⟩, 3/640⟩
def center2249 : GaussianRat :=
  ⟨5469449/200000000, 51168439/200000000⟩
def contact2249 : RatBall := localContactBall tau2249 center2249
def work2249 : RoundedTauEval :=
  evalTau precision tau2249 contact2249 logTwoBall

theorem center_sq2249 : (center2249.re : ℝ)^2 +
    (center2249.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2249]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2249 : work2249.theta.ok = true ∧
    work2249.jac.invOK = true ∧ acceptsUnitSq work2249.out = true := by decide +kernel

def cell2249 : CellCertificate where
  tauBall := tau2249
  contactCenter := center2249
  contactBall := contact2249
  work := work2249
  center_sq := center_sq2249
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2249.1
  jac_ok := checks2249.2.1
  accepted := checks2249.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281


