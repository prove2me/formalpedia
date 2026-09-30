-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0362_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0362_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:15:52.390991+00:00
-- url     : https://prove2.me/theorems/af4f41ab-98c8-4913-91cd-72c4d9a72972
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0362 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2896 : RatBall :=
  ⟨⟨1/128, -251/640⟩, 3/1280⟩
def center2896 : GaussianRat :=
  ⟨3221293/500000000, -287852971/1000000000⟩
def contact2896 : RatBall := localContactBall tau2896 center2896
def work2896 : RoundedTauEval :=
  evalTau precision tau2896 contact2896 logTwoBall

theorem center_sq2896 : (center2896.re : ℝ)^2 +
    (center2896.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2896]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2896 : work2896.theta.ok = true ∧
    work2896.jac.invOK = true ∧ acceptsUnitSq work2896.out = true := by decide +kernel

def cell2896 : CellCertificate where
  tauBall := tau2896
  contactCenter := center2896
  contactBall := contact2896
  work := work2896
  center_sq := center_sq2896
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2896.1
  jac_ok := checks2896.2.1
  accepted := checks2896.2.2

def tau2897 : RatBall :=
  ⟨⟨7/640, -251/640⟩, 3/1280⟩
def center2897 : GaussianRat :=
  ⟨9019241/1000000000, -287829653/1000000000⟩
def contact2897 : RatBall := localContactBall tau2897 center2897
def work2897 : RoundedTauEval :=
  evalTau precision tau2897 contact2897 logTwoBall

theorem center_sq2897 : (center2897.re : ℝ)^2 +
    (center2897.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2897]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2897 : work2897.theta.ok = true ∧
    work2897.jac.invOK = true ∧ acceptsUnitSq work2897.out = true := by decide +kernel

def cell2897 : CellCertificate where
  tauBall := tau2897
  contactCenter := center2897
  contactBall := contact2897
  work := work2897
  center_sq := center_sq2897
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2897.1
  jac_ok := checks2897.2.1
  accepted := checks2897.2.2

def tau2898 : RatBall :=
  ⟨⟨1/128, -249/640⟩, 3/1280⟩
def center2898 : GaussianRat :=
  ⟨6423287/1000000000, -285280029/1000000000⟩
def contact2898 : RatBall := localContactBall tau2898 center2898
def work2898 : RoundedTauEval :=
  evalTau precision tau2898 contact2898 logTwoBall

theorem center_sq2898 : (center2898.re : ℝ)^2 +
    (center2898.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2898]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2898 : work2898.theta.ok = true ∧
    work2898.jac.invOK = true ∧ acceptsUnitSq work2898.out = true := by decide +kernel

def cell2898 : CellCertificate where
  tauBall := tau2898
  contactCenter := center2898
  contactBall := contact2898
  work := work2898
  center_sq := center_sq2898
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2898.1
  jac_ok := checks2898.2.1
  accepted := checks2898.2.2

def tau2899 : RatBall :=
  ⟨⟨7/640, -249/640⟩, 3/1280⟩
def center2899 : GaussianRat :=
  ⟨2248057/250000000, -142628517/500000000⟩
def contact2899 : RatBall := localContactBall tau2899 center2899
def work2899 : RoundedTauEval :=
  evalTau precision tau2899 contact2899 logTwoBall

theorem center_sq2899 : (center2899.re : ℝ)^2 +
    (center2899.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2899]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2899 : work2899.theta.ok = true ∧
    work2899.jac.invOK = true ∧ acceptsUnitSq work2899.out = true := by decide +kernel

def cell2899 : CellCertificate where
  tauBall := tau2899
  contactCenter := center2899
  contactBall := contact2899
  work := work2899
  center_sq := center_sq2899
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2899.1
  jac_ok := checks2899.2.1
  accepted := checks2899.2.2

def tau2900 : RatBall :=
  ⟨⟨9/640, -51/128⟩, 3/1280⟩
def center2900 : GaussianRat :=
  ⟨11666429/1000000000, -4577599/15625000⟩
def contact2900 : RatBall := localContactBall tau2900 center2900
def work2900 : RoundedTauEval :=
  evalTau precision tau2900 contact2900 logTwoBall

theorem center_sq2900 : (center2900.re : ℝ)^2 +
    (center2900.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2900]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2900 : work2900.theta.ok = true ∧
    work2900.jac.invOK = true ∧ acceptsUnitSq work2900.out = true := by decide +kernel

def cell2900 : CellCertificate where
  tauBall := tau2900
  contactCenter := center2900
  contactBall := contact2900
  work := work2900
  center_sq := center_sq2900
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2900.1
  jac_ok := checks2900.2.1
  accepted := checks2900.2.2

def tau2901 : RatBall :=
  ⟨⟨11/640, -51/128⟩, 3/1280⟩
def center2901 : GaussianRat :=
  ⟨3564487/250000000, -73231599/250000000⟩
def contact2901 : RatBall := localContactBall tau2901 center2901
def work2901 : RoundedTauEval :=
  evalTau precision tau2901 contact2901 logTwoBall

theorem center_sq2901 : (center2901.re : ℝ)^2 +
    (center2901.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2901]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2901 : work2901.theta.ok = true ∧
    work2901.jac.invOK = true ∧ acceptsUnitSq work2901.out = true := by decide +kernel

def cell2901 : CellCertificate where
  tauBall := tau2901
  contactCenter := center2901
  contactBall := contact2901
  work := work2901
  center_sq := center_sq2901
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2901.1
  jac_ok := checks2901.2.1
  accepted := checks2901.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362


