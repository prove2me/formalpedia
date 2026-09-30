-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0263_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0263_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:16:49.139433+00:00
-- url     : https://prove2.me/theorems/b58806bc-40e2-4557-b495-e7e00cc9be9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0263 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2104 : RatBall :=
  ⟨⟨-37/320, 107/320⟩, 3/640⟩
def center2104 : GaussianRat :=
  ⟨-22489569/250000000, 47478823/200000000⟩
def contact2104 : RatBall := localContactBall tau2104 center2104
def work2104 : RoundedTauEval :=
  evalTau precision tau2104 contact2104 logTwoBall

theorem center_sq2104 : (center2104.re : ℝ)^2 +
    (center2104.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2104]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2104 : work2104.theta.ok = true ∧
    work2104.jac.invOK = true ∧ acceptsUnitSq work2104.out = true := by decide +kernel

def cell2104 : CellCertificate where
  tauBall := tau2104
  contactCenter := center2104
  contactBall := contact2104
  work := work2104
  center_sq := center_sq2104
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2104.1
  jac_ok := checks2104.2.1
  accepted := checks2104.2.2

def tau2105 : RatBall :=
  ⟨⟨-39/320, 109/320⟩, 3/640⟩
def center2105 : GaussianRat :=
  ⟨-47597289/500000000, 241742219/1000000000⟩
def contact2105 : RatBall := localContactBall tau2105 center2105
def work2105 : RoundedTauEval :=
  evalTau precision tau2105 contact2105 logTwoBall

theorem center_sq2105 : (center2105.re : ℝ)^2 +
    (center2105.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2105]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2105 : work2105.theta.ok = true ∧
    work2105.jac.invOK = true ∧ acceptsUnitSq work2105.out = true := by decide +kernel

def cell2105 : CellCertificate where
  tauBall := tau2105
  contactCenter := center2105
  contactBall := contact2105
  work := work2105
  center_sq := center_sq2105
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2105.1
  jac_ok := checks2105.2.1
  accepted := checks2105.2.2

def tau2106 : RatBall :=
  ⟨⟨-37/320, 109/320⟩, 3/640⟩
def center2106 : GaussianRat :=
  ⟨-45195779/500000000, 121096227/500000000⟩
def contact2106 : RatBall := localContactBall tau2106 center2106
def work2106 : RoundedTauEval :=
  evalTau precision tau2106 contact2106 logTwoBall

theorem center_sq2106 : (center2106.re : ℝ)^2 +
    (center2106.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2106]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2106 : work2106.theta.ok = true ∧
    work2106.jac.invOK = true ∧ acceptsUnitSq work2106.out = true := by decide +kernel

def cell2106 : CellCertificate where
  tauBall := tau2106
  contactCenter := center2106
  contactBall := contact2106
  work := work2106
  center_sq := center_sq2106
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2106.1
  jac_ok := checks2106.2.1
  accepted := checks2106.2.2

def tau2107 : RatBall :=
  ⟨⟨-39/320, 111/320⟩, 3/640⟩
def center2107 : GaussianRat :=
  ⟨-11957763/125000000, 15409367/62500000⟩
def contact2107 : RatBall := localContactBall tau2107 center2107
def work2107 : RoundedTauEval :=
  evalTau precision tau2107 contact2107 logTwoBall

theorem center_sq2107 : (center2107.re : ℝ)^2 +
    (center2107.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2107 : work2107.theta.ok = true ∧
    work2107.jac.invOK = true ∧ acceptsUnitSq work2107.out = true := by decide +kernel

def cell2107 : CellCertificate where
  tauBall := tau2107
  contactCenter := center2107
  contactBall := contact2107
  work := work2107
  center_sq := center_sq2107
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2107.1
  jac_ok := checks2107.2.1
  accepted := checks2107.2.2

def tau2108 : RatBall :=
  ⟨⟨-37/320, 111/320⟩, 3/640⟩
def center2108 : GaussianRat :=
  ⟨-45418507/500000000, 247012717/1000000000⟩
def contact2108 : RatBall := localContactBall tau2108 center2108
def work2108 : RoundedTauEval :=
  evalTau precision tau2108 contact2108 logTwoBall

theorem center_sq2108 : (center2108.re : ℝ)^2 +
    (center2108.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2108 : work2108.theta.ok = true ∧
    work2108.jac.invOK = true ∧ acceptsUnitSq work2108.out = true := by decide +kernel

def cell2108 : CellCertificate where
  tauBall := tau2108
  contactCenter := center2108
  contactBall := contact2108
  work := work2108
  center_sq := center_sq2108
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2108.1
  jac_ok := checks2108.2.1
  accepted := checks2108.2.2

def tau2109 : RatBall :=
  ⟨⟨-7/64, 109/320⟩, 3/640⟩
def center2109 : GaussianRat :=
  ⟨-17115273/200000000, 242620769/1000000000⟩
def contact2109 : RatBall := localContactBall tau2109 center2109
def work2109 : RoundedTauEval :=
  evalTau precision tau2109 contact2109 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263


