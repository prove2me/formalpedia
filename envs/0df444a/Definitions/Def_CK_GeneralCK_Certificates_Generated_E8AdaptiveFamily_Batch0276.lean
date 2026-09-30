-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0276
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0276
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:18:32.533178+00:00
-- url     : https://prove2.me/theorems/3a8594ec-5f02-43e0-bc73-56a8b940a659
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0276.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0276_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell2213 : CellCertificate where
  tauBall := tau2213
  contactCenter := center2213
  contactBall := contact2213
  work := work2213
  center_sq := center_sq2213
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2213.1
  jac_ok := checks2213.2.1
  accepted := checks2213.2.2

def tau2214 : RatBall :=
  ⟨⟨-9/320, 123/320⟩, 3/640⟩
def center2214 : GaussianRat :=
  ⟨-11504853/500000000, 2811547/10000000⟩
def contact2214 : RatBall := localContactBall tau2214 center2214
def work2214 : RoundedTauEval :=
  evalTau precision tau2214 contact2214 logTwoBall

theorem center_sq2214 : (center2214.re : ℝ)^2 +
    (center2214.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2214]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2214 : work2214.theta.ok = true ∧
    work2214.jac.invOK = true ∧ acceptsUnitSq work2214.out = true := by decide +kernel

def cell2214 : CellCertificate where
  tauBall := tau2214
  contactCenter := center2214
  contactBall := contact2214
  work := work2214
  center_sq := center_sq2214
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2214.1
  jac_ok := checks2214.2.1
  accepted := checks2214.2.2

def tau2215 : RatBall :=
  ⟨⟨-7/320, 121/320⟩, 3/640⟩
def center2215 : GaussianRat :=
  ⟨-2224603/125000000, 539411/1953125⟩
def contact2215 : RatBall := localContactBall tau2215 center2215
def work2215 : RoundedTauEval :=
  evalTau precision tau2215 contact2215 logTwoBall

theorem center_sq2215 : (center2215.re : ℝ)^2 +
    (center2215.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2215]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2215 : work2215.theta.ok = true ∧
    work2215.jac.invOK = true ∧ acceptsUnitSq work2215.out = true := by decide +kernel

def cell2215 : CellCertificate where
  tauBall := tau2215
  contactCenter := center2215
  contactBall := contact2215
  work := work2215
  center_sq := center_sq2215
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2215.1
  jac_ok := checks2215.2.1
  accepted := checks2215.2.2

def cells : List CellCertificate := [cell2208, cell2209, cell2210, cell2211, cell2212, cell2213, cell2214, cell2215]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276


