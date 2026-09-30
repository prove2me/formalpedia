-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0261_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0261_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:30:04.748827+00:00
-- url     : https://prove2.me/theorems/9b3a9928-73c8-47f7-9cca-6f417a92ddb1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0261 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2088 : RatBall :=
  ⟨⟨-9/64, 107/320⟩, 3/640⟩
def center2088 : GaussianRat :=
  ⟨-109007417/1000000000, 235517221/1000000000⟩
def contact2088 : RatBall := localContactBall tau2088 center2088
def work2088 : RoundedTauEval :=
  evalTau precision tau2088 contact2088 logTwoBall

theorem center_sq2088 : (center2088.re : ℝ)^2 +
    (center2088.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2088]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2088 : work2088.theta.ok = true ∧
    work2088.jac.invOK = true ∧ acceptsUnitSq work2088.out = true := by decide +kernel

def cell2088 : CellCertificate where
  tauBall := tau2088
  contactCenter := center2088
  contactBall := contact2088
  work := work2088
  center_sq := center_sq2088
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2088.1
  jac_ok := checks2088.2.1
  accepted := checks2088.2.2

def tau2089 : RatBall :=
  ⟨⟨-43/320, 21/64⟩, 3/640⟩
def center2089 : GaussianRat :=
  ⟨-103781603/1000000000, 28909781/125000000⟩
def contact2089 : RatBall := localContactBall tau2089 center2089
def work2089 : RoundedTauEval :=
  evalTau precision tau2089 contact2089 logTwoBall

theorem center_sq2089 : (center2089.re : ℝ)^2 +
    (center2089.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2089]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2089 : work2089.theta.ok = true ∧
    work2089.jac.invOK = true ∧ acceptsUnitSq work2089.out = true := by decide +kernel

def cell2089 : CellCertificate where
  tauBall := tau2089
  contactCenter := center2089
  contactBall := contact2089
  work := work2089
  center_sq := center_sq2089
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2089.1
  jac_ok := checks2089.2.1
  accepted := checks2089.2.2

def tau2090 : RatBall :=
  ⟨⟨-41/320, 21/64⟩, 3/640⟩
def center2090 : GaussianRat :=
  ⟨-12380739/125000000, 115872433/500000000⟩
def contact2090 : RatBall := localContactBall tau2090 center2090
def work2090 : RoundedTauEval :=
  evalTau precision tau2090 contact2090 logTwoBall

theorem center_sq2090 : (center2090.re : ℝ)^2 +
    (center2090.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2090]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2090 : work2090.theta.ok = true ∧
    work2090.jac.invOK = true ∧ acceptsUnitSq work2090.out = true := by decide +kernel

def cell2090 : CellCertificate where
  tauBall := tau2090
  contactCenter := center2090
  contactBall := contact2090
  work := work2090
  center_sq := center_sq2090
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2090.1
  jac_ok := checks2090.2.1
  accepted := checks2090.2.2

def tau2091 : RatBall :=
  ⟨⟨-43/320, 107/320⟩, 3/640⟩
def center2091 : GaussianRat :=
  ⟨-104264923/1000000000, 236017459/1000000000⟩
def contact2091 : RatBall := localContactBall tau2091 center2091
def work2091 : RoundedTauEval :=
  evalTau precision tau2091 contact2091 logTwoBall

theorem center_sq2091 : (center2091.re : ℝ)^2 +
    (center2091.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2091]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2091 : work2091.theta.ok = true ∧
    work2091.jac.invOK = true ∧ acceptsUnitSq work2091.out = true := by decide +kernel

def cell2091 : CellCertificate where
  tauBall := tau2091
  contactCenter := center2091
  contactBall := contact2091
  work := work2091
  center_sq := center_sq2091
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2091.1
  jac_ok := checks2091.2.1
  accepted := checks2091.2.2

def tau2092 : RatBall :=
  ⟨⟨-41/320, 107/320⟩, 3/640⟩
def center2092 : GaussianRat :=
  ⟨-99508871/1000000000, 236497219/1000000000⟩
def contact2092 : RatBall := localContactBall tau2092 center2092
def work2092 : RoundedTauEval :=
  evalTau precision tau2092 contact2092 logTwoBall

theorem center_sq2092 : (center2092.re : ℝ)^2 +
    (center2092.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2092]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2092 : work2092.theta.ok = true ∧
    work2092.jac.invOK = true ∧ acceptsUnitSq work2092.out = true := by decide +kernel

def cell2092 : CellCertificate where
  tauBall := tau2092
  contactCenter := center2092
  contactBall := contact2092
  work := work2092
  center_sq := center_sq2092
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2092.1
  jac_ok := checks2092.2.1
  accepted := checks2092.2.2

def tau2093 : RatBall :=
  ⟨⟨-47/320, 109/320⟩, 3/640⟩
def center2093 : GaussianRat :=
  ⟨-3571049/31250000, 239728011/1000000000⟩
def contact2093 : RatBall := localContactBall tau2093 center2093
def work2093 : RoundedTauEval :=
  evalTau precision tau2093 contact2093 logTwoBall

theorem center_sq2093 : (center2093.re : ℝ)^2 +
    (center2093.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2093]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261


