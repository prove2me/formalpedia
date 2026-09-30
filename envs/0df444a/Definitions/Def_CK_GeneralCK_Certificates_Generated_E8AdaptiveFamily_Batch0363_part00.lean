-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0363_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0363_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:12:46.653306+00:00
-- url     : https://prove2.me/theorems/a124e690-f109-447c-95a5-a3448f1d0cbe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0363 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2904 : RatBall :=
  ⟨⟨13/640, -51/128⟩, 3/1280⟩
def center2904 : GaussianRat :=
  ⟨3369771/200000000, -146439243/500000000⟩
def contact2904 : RatBall := localContactBall tau2904 center2904
def work2904 : RoundedTauEval :=
  evalTau precision tau2904 contact2904 logTwoBall

theorem center_sq2904 : (center2904.re : ℝ)^2 +
    (center2904.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2904]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2904 : work2904.theta.ok = true ∧
    work2904.jac.invOK = true ∧ acceptsUnitSq work2904.out = true := by decide +kernel

def cell2904 : CellCertificate where
  tauBall := tau2904
  contactCenter := center2904
  contactBall := contact2904
  work := work2904
  center_sq := center_sq2904
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2904.1
  jac_ok := checks2904.2.1
  accepted := checks2904.2.2

def tau2905 : RatBall :=
  ⟨⟨3/128, -51/128⟩, 3/1280⟩
def center2905 : GaussianRat :=
  ⟨60747/3125000, -58564523/200000000⟩
def contact2905 : RatBall := localContactBall tau2905 center2905
def work2905 : RoundedTauEval :=
  evalTau precision tau2905 contact2905 logTwoBall

theorem center_sq2905 : (center2905.re : ℝ)^2 +
    (center2905.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2905]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2905 : work2905.theta.ok = true ∧
    work2905.jac.invOK = true ∧ acceptsUnitSq work2905.out = true := by decide +kernel

def cell2905 : CellCertificate where
  tauBall := tau2905
  contactCenter := center2905
  contactBall := contact2905
  work := work2905
  center_sq := center_sq2905
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2905.1
  jac_ok := checks2905.2.1
  accepted := checks2905.2.2

def tau2906 : RatBall :=
  ⟨⟨13/640, -253/640⟩, 3/1280⟩
def center2906 : GaussianRat :=
  ⟨16797323/1000000000, -290291883/1000000000⟩
def contact2906 : RatBall := localContactBall tau2906 center2906
def work2906 : RoundedTauEval :=
  evalTau precision tau2906 contact2906 logTwoBall

theorem center_sq2906 : (center2906.re : ℝ)^2 +
    (center2906.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2906]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2906 : work2906.theta.ok = true ∧
    work2906.jac.invOK = true ∧ acceptsUnitSq work2906.out = true := by decide +kernel

def cell2906 : CellCertificate where
  tauBall := tau2906
  contactCenter := center2906
  contactBall := contact2906
  work := work2906
  center_sq := center_sq2906
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2906.1
  jac_ok := checks2906.2.1
  accepted := checks2906.2.2

def tau2907 : RatBall :=
  ⟨⟨3/128, -253/640⟩, 3/1280⟩
def center2907 : GaussianRat :=
  ⟨19379607/1000000000, -58047357/200000000⟩
def contact2907 : RatBall := localContactBall tau2907 center2907
def work2907 : RoundedTauEval :=
  evalTau precision tau2907 contact2907 logTwoBall

theorem center_sq2907 : (center2907.re : ℝ)^2 +
    (center2907.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2907]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2907 : work2907.theta.ok = true ∧
    work2907.jac.invOK = true ∧ acceptsUnitSq work2907.out = true := by decide +kernel

def cell2907 : CellCertificate where
  tauBall := tau2907
  contactCenter := center2907
  contactBall := contact2907
  work := work2907
  center_sq := center_sq2907
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2907.1
  jac_ok := checks2907.2.1
  accepted := checks2907.2.2

def tau2908 : RatBall :=
  ⟨⟨9/640, -251/640⟩, 3/1280⟩
def center2908 : GaussianRat :=
  ⟨5797759/500000000, -28779857/100000000⟩
def contact2908 : RatBall := localContactBall tau2908 center2908
def work2908 : RoundedTauEval :=
  evalTau precision tau2908 contact2908 logTwoBall

theorem center_sq2908 : (center2908.re : ℝ)^2 +
    (center2908.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2908]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2908 : work2908.theta.ok = true ∧
    work2908.jac.invOK = true ∧ acceptsUnitSq work2908.out = true := by decide +kernel

def cell2908 : CellCertificate where
  tauBall := tau2908
  contactCenter := center2908
  contactBall := contact2908
  work := work2908
  center_sq := center_sq2908
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2908.1
  jac_ok := checks2908.2.1
  accepted := checks2908.2.2

def tau2909 : RatBall :=
  ⟨⟨11/640, -251/640⟩, 3/1280⟩
def center2909 : GaussianRat :=
  ⟨14171307/1000000000, -287759727/1000000000⟩
def contact2909 : RatBall := localContactBall tau2909 center2909
def work2909 : RoundedTauEval :=
  evalTau precision tau2909 contact2909 logTwoBall

theorem center_sq2909 : (center2909.re : ℝ)^2 +
    (center2909.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2909]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2909 : work2909.theta.ok = true ∧
    work2909.jac.invOK = true ∧ acceptsUnitSq work2909.out = true := by decide +kernel

def cell2909 : CellCertificate where
  tauBall := tau2909
  contactCenter := center2909
  contactBall := contact2909
  work := work2909
  center_sq := center_sq2909
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2909.1
  jac_ok := checks2909.2.1
  accepted := checks2909.2.2

def tau2910 : RatBall :=
  ⟨⟨9/640, -249/640⟩, 3/1280⟩
def center2910 : GaussianRat :=
  ⟨2890199/250000000, -14261319/50000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363


