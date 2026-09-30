-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0305
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0305
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:23:31.289698+00:00
-- url     : https://prove2.me/theorems/17f8b633-8d3a-4cf5-9bca-dce81d532988
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0305.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0305_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2444 : work2444.theta.ok = true ∧
    work2444.jac.invOK = true ∧ acceptsUnitSq work2444.out = true := by decide +kernel

def cell2444 : CellCertificate where
  tauBall := tau2444
  contactCenter := center2444
  contactBall := contact2444
  work := work2444
  center_sq := center_sq2444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2444.1
  jac_ok := checks2444.2.1
  accepted := checks2444.2.2

def tau2445 : RatBall :=
  ⟨⟨79/320, 93/320⟩, 3/640⟩
def center2445 : GaussianRat :=
  ⟨90986481/500000000, 24189551/125000000⟩
def contact2445 : RatBall := localContactBall tau2445 center2445
def work2445 : RoundedTauEval :=
  evalTau precision tau2445 contact2445 logTwoBall

theorem center_sq2445 : (center2445.re : ℝ)^2 +
    (center2445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2445 : work2445.theta.ok = true ∧
    work2445.jac.invOK = true ∧ acceptsUnitSq work2445.out = true := by decide +kernel

def cell2445 : CellCertificate where
  tauBall := tau2445
  contactCenter := center2445
  contactBall := contact2445
  work := work2445
  center_sq := center_sq2445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2445.1
  jac_ok := checks2445.2.1
  accepted := checks2445.2.2

def tau2446 : RatBall :=
  ⟨⟨77/320, 19/64⟩, 3/640⟩
def center2446 : GaussianRat :=
  ⟨35656681/200000000, 198539511/1000000000⟩
def contact2446 : RatBall := localContactBall tau2446 center2446
def work2446 : RoundedTauEval :=
  evalTau precision tau2446 contact2446 logTwoBall

theorem center_sq2446 : (center2446.re : ℝ)^2 +
    (center2446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2446 : work2446.theta.ok = true ∧
    work2446.jac.invOK = true ∧ acceptsUnitSq work2446.out = true := by decide +kernel

def cell2446 : CellCertificate where
  tauBall := tau2446
  contactCenter := center2446
  contactBall := contact2446
  work := work2446
  center_sq := center_sq2446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2446.1
  jac_ok := checks2446.2.1
  accepted := checks2446.2.2

def tau2447 : RatBall :=
  ⟨⟨79/320, 19/64⟩, 3/640⟩
def center2447 : GaussianRat :=
  ⟨91322907/500000000, 98931697/500000000⟩
def contact2447 : RatBall := localContactBall tau2447 center2447
def work2447 : RoundedTauEval :=
  evalTau precision tau2447 contact2447 logTwoBall

theorem center_sq2447 : (center2447.re : ℝ)^2 +
    (center2447.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2447]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2447 : work2447.theta.ok = true ∧
    work2447.jac.invOK = true ∧ acceptsUnitSq work2447.out = true := by decide +kernel

def cell2447 : CellCertificate where
  tauBall := tau2447
  contactCenter := center2447
  contactBall := contact2447
  work := work2447
  center_sq := center_sq2447
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2447.1
  jac_ok := checks2447.2.1
  accepted := checks2447.2.2

def cells : List CellCertificate := [cell2440, cell2441, cell2442, cell2443, cell2444, cell2445, cell2446, cell2447]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305


