-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0283
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0283
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:30:42.029799+00:00
-- url     : https://prove2.me/theorems/2ce1a760-3c9a-48c9-899e-053c1ff53529
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0283.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2264 : RatBall :=
  ⟨⟨1/320, 121/320⟩, 3/640⟩
def center2264 : GaussianRat :=
  ⟨2543217/1000000000, 276353553/1000000000⟩
def contact2264 : RatBall := localContactBall tau2264 center2264
def work2264 : RoundedTauEval :=
  evalTau precision tau2264 contact2264 logTwoBall

theorem center_sq2264 : (center2264.re : ℝ)^2 +
    (center2264.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2264]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2264 : work2264.theta.ok = true ∧
    work2264.jac.invOK = true ∧ acceptsUnitSq work2264.out = true := by decide +kernel

def cell2264 : CellCertificate where
  tauBall := tau2264
  contactCenter := center2264
  contactBall := contact2264
  work := work2264
  center_sq := center_sq2264
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2264.1
  jac_ok := checks2264.2.1
  accepted := checks2264.2.2

def tau2265 : RatBall :=
  ⟨⟨3/320, 121/320⟩, 3/640⟩
def center2265 : GaussianRat :=
  ⟨1907311/250000000, 69081087/250000000⟩
def contact2265 : RatBall := localContactBall tau2265 center2265
def work2265 : RoundedTauEval :=
  evalTau precision tau2265 contact2265 logTwoBall

theorem center_sq2265 : (center2265.re : ℝ)^2 +
    (center2265.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2265 : work2265.theta.ok = true ∧
    work2265.jac.invOK = true ∧ acceptsUnitSq work2265.out = true := by decide +kernel

def cell2265 : CellCertificate where
  tauBall := tau2265
  contactCenter := center2265
  contactBall := contact2265
  work := work2265
  center_sq := center_sq2265
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2265.1
  jac_ok := checks2265.2.1
  accepted := checks2265.2.2

def tau2266 : RatBall :=
  ⟨⟨1/320, 123/320⟩, 3/640⟩
def center2266 : GaussianRat :=
  ⟨2558027/1000000000, 14072733/50000000⟩
def contact2266 : RatBall := localContactBall tau2266 center2266
def work2266 : RoundedTauEval :=
  evalTau precision tau2266 contact2266 logTwoBall

theorem center_sq2266 : (center2266.re : ℝ)^2 +
    (center2266.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2266]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2266 : work2266.theta.ok = true ∧
    work2266.jac.invOK = true ∧ acceptsUnitSq work2266.out = true := by decide +kernel

def cell2266 : CellCertificate where
  tauBall := tau2266
  contactCenter := center2266
  contactBall := contact2266
  work := work2266
  center_sq := center_sq2266
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2266.1
  jac_ok := checks2266.2.1
  accepted := checks2266.2.2

def tau2267 : RatBall :=
  ⟨⟨3/320, 123/320⟩, 3/640⟩
def center2267 : GaussianRat :=
  ⟨3836831/500000000, 281424629/1000000000⟩
def contact2267 : RatBall := localContactBall tau2267 center2267
def work2267 : RoundedTauEval :=
  evalTau precision tau2267 contact2267 logTwoBall

theorem center_sq2267 : (center2267.re : ℝ)^2 +
    (center2267.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2267]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2267 : work2267.theta.ok = true ∧
    work2267.jac.invOK = true ∧ acceptsUnitSq work2267.out = true := by decide +kernel

def cell2267 : CellCertificate where
  tauBall := tau2267
  contactCenter := center2267
  contactBall := contact2267
  work := work2267
  center_sq := center_sq2267
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2267.1
  jac_ok := checks2267.2.1
  accepted := checks2267.2.2

def tau2268 : RatBall :=
  ⟨⟨1/64, 121/320⟩, 3/640⟩
def center2268 : GaussianRat :=
  ⟨254281/20000000, 276265959/1000000000⟩
def contact2268 : RatBall := localContactBall tau2268 center2268
def work2268 : RoundedTauEval :=
  evalTau precision tau2268 contact2268 logTwoBall

theorem center_sq2268 : (center2268.re : ℝ)^2 +
    (center2268.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2268]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2268 : work2268.theta.ok = true ∧
    work2268.jac.invOK = true ∧ acceptsUnitSq work2268.out = true := by decide +kernel

def cell2268 : CellCertificate where
  tauBall := tau2268
  contactCenter := center2268
  contactBall := contact2268
  work := work2268
  center_sq := center_sq2268
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2268.1
  jac_ok := checks2268.2.1
  accepted := checks2268.2.2

def tau2269 : RatBall :=
  ⟨⟨7/320, 121/320⟩, 3/640⟩
def center2269 : GaussianRat :=
  ⟨2224603/125000000, 539411/1953125⟩
def contact2269 : RatBall := localContactBall tau2269 center2269
def work2269 : RoundedTauEval :=
  evalTau precision tau2269 contact2269 logTwoBall

theorem center_sq2269 : (center2269.re : ℝ)^2 +
    (center2269.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2269]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2269 : work2269.theta.ok = true ∧
    work2269.jac.invOK = true ∧ acceptsUnitSq work2269.out = true := by decide +kernel

def cell2269 : CellCertificate where
  tauBall := tau2269
  contactCenter := center2269
  contactBall := contact2269
  work := work2269
  center_sq := center_sq2269
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2269.1
  jac_ok := checks2269.2.1
  accepted := checks2269.2.2

def tau2270 : RatBall :=
  ⟨⟨1/64, 123/320⟩, 3/640⟩
def center2270 : GaussianRat :=
  ⟨12788043/1000000000, 281364591/1000000000⟩
def contact2270 : RatBall := localContactBall tau2270 center2270
def work2270 : RoundedTauEval :=
  evalTau precision tau2270 contact2270 logTwoBall

theorem center_sq2270 : (center2270.re : ℝ)^2 +
    (center2270.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2270]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2270 : work2270.theta.ok = true ∧
    work2270.jac.invOK = true ∧ acceptsUnitSq work2270.out = true := by decide +kernel

def cell2270 : CellCertificate where
  tauBall := tau2270
  contactCenter := center2270
  contactBall := contact2270
  work := work2270
  center_sq := center_sq2270
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2270.1
  jac_ok := checks2270.2.1
  accepted := checks2270.2.2

def tau2271 : RatBall :=
  ⟨⟨7/320, 123/320⟩, 3/640⟩
def center2271 : GaussianRat :=
  ⟨3580067/200000000, 8789831/31250000⟩
def contact2271 : RatBall := localContactBall tau2271 center2271
def work2271 : RoundedTauEval :=
  evalTau precision tau2271 contact2271 logTwoBall

theorem center_sq2271 : (center2271.re : ℝ)^2 +
    (center2271.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2271]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2271 : work2271.theta.ok = true ∧
    work2271.jac.invOK = true ∧ acceptsUnitSq work2271.out = true := by decide +kernel

def cell2271 : CellCertificate where
  tauBall := tau2271
  contactCenter := center2271
  contactBall := contact2271
  work := work2271
  center_sq := center_sq2271
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2271.1
  jac_ok := checks2271.2.1
  accepted := checks2271.2.2

def cells : List CellCertificate := [cell2264, cell2265, cell2266, cell2267, cell2268, cell2269, cell2270, cell2271]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283

end


