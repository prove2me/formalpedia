-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0373
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0373
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:35:52.489987+00:00
-- url     : https://prove2.me/theorems/1a3b9ab7-77cc-4941-b375-57a09e3f5070
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0373.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2984 : RatBall :=
  ⟨⟨7/128, -247/640⟩, 3/1280⟩
def center2984 : GaussianRat :=
  ⟨2796129/62500000, -281586221/1000000000⟩
def contact2984 : RatBall := localContactBall tau2984 center2984
def work2984 : RoundedTauEval :=
  evalTau precision tau2984 contact2984 logTwoBall

theorem center_sq2984 : (center2984.re : ℝ)^2 +
    (center2984.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2984]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2984 : work2984.theta.ok = true ∧
    work2984.jac.invOK = true ∧ acceptsUnitSq work2984.out = true := by decide +kernel

def cell2984 : CellCertificate where
  tauBall := tau2984
  contactCenter := center2984
  contactBall := contact2984
  work := work2984
  center_sq := center_sq2984
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2984.1
  jac_ok := checks2984.2.1
  accepted := checks2984.2.2

def tau2985 : RatBall :=
  ⟨⟨33/640, -49/128⟩, 3/1280⟩
def center2985 : GaussianRat :=
  ⟨42068541/1000000000, -27916967/100000000⟩
def contact2985 : RatBall := localContactBall tau2985 center2985
def work2985 : RoundedTauEval :=
  evalTau precision tau2985 contact2985 logTwoBall

theorem center_sq2985 : (center2985.re : ℝ)^2 +
    (center2985.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2985]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2985 : work2985.theta.ok = true ∧
    work2985.jac.invOK = true ∧ acceptsUnitSq work2985.out = true := by decide +kernel

def cell2985 : CellCertificate where
  tauBall := tau2985
  contactCenter := center2985
  contactBall := contact2985
  work := work2985
  center_sq := center_sq2985
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2985.1
  jac_ok := checks2985.2.1
  accepted := checks2985.2.2

def tau2986 : RatBall :=
  ⟨⟨7/128, -49/128⟩, 3/1280⟩
def center2986 : GaussianRat :=
  ⟨44607937/1000000000, -279044067/1000000000⟩
def contact2986 : RatBall := localContactBall tau2986 center2986
def work2986 : RoundedTauEval :=
  evalTau precision tau2986 contact2986 logTwoBall

theorem center_sq2986 : (center2986.re : ℝ)^2 +
    (center2986.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2986]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2986 : work2986.theta.ok = true ∧
    work2986.jac.invOK = true ∧ acceptsUnitSq work2986.out = true := by decide +kernel

def cell2986 : CellCertificate where
  tauBall := tau2986
  contactCenter := center2986
  contactBall := contact2986
  work := work2986
  center_sq := center_sq2986
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2986.1
  jac_ok := checks2986.2.1
  accepted := checks2986.2.2

def tau2987 : RatBall :=
  ⟨⟨37/640, -247/640⟩, 3/1280⟩
def center2987 : GaussianRat :=
  ⟨11820737/250000000, -11258061/40000000⟩
def contact2987 : RatBall := localContactBall tau2987 center2987
def work2987 : RoundedTauEval :=
  evalTau precision tau2987 contact2987 logTwoBall

theorem center_sq2987 : (center2987.re : ℝ)^2 +
    (center2987.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2987]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2987 : work2987.theta.ok = true ∧
    work2987.jac.invOK = true ∧ acceptsUnitSq work2987.out = true := by decide +kernel

def cell2987 : CellCertificate where
  tauBall := tau2987
  contactCenter := center2987
  contactBall := contact2987
  work := work2987
  center_sq := center_sq2987
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2987.1
  jac_ok := checks2987.2.1
  accepted := checks2987.2.2

def tau2988 : RatBall :=
  ⟨⟨39/640, -247/640⟩, 3/1280⟩
def center2988 : GaussianRat :=
  ⟨49825917/1000000000, -281309513/1000000000⟩
def contact2988 : RatBall := localContactBall tau2988 center2988
def work2988 : RoundedTauEval :=
  evalTau precision tau2988 contact2988 logTwoBall

theorem center_sq2988 : (center2988.re : ℝ)^2 +
    (center2988.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2988]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2988 : work2988.theta.ok = true ∧
    work2988.jac.invOK = true ∧ acceptsUnitSq work2988.out = true := by decide +kernel

def cell2988 : CellCertificate where
  tauBall := tau2988
  contactCenter := center2988
  contactBall := contact2988
  work := work2988
  center_sq := center_sq2988
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2988.1
  jac_ok := checks2988.2.1
  accepted := checks2988.2.2

def tau2989 : RatBall :=
  ⟨⟨37/640, -49/128⟩, 3/1280⟩
def center2989 : GaussianRat :=
  ⟨23572771/500000000, -278911223/1000000000⟩
def contact2989 : RatBall := localContactBall tau2989 center2989
def work2989 : RoundedTauEval :=
  evalTau precision tau2989 contact2989 logTwoBall

theorem center_sq2989 : (center2989.re : ℝ)^2 +
    (center2989.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2989]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2989 : work2989.theta.ok = true ∧
    work2989.jac.invOK = true ∧ acceptsUnitSq work2989.out = true := by decide +kernel

def cell2989 : CellCertificate where
  tauBall := tau2989
  contactCenter := center2989
  contactBall := contact2989
  work := work2989
  center_sq := center_sq2989
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2989.1
  jac_ok := checks2989.2.1
  accepted := checks2989.2.2

def tau2990 : RatBall :=
  ⟨⟨39/640, -49/128⟩, 3/1280⟩
def center2990 : GaussianRat :=
  ⟨49681259/1000000000, -139385581/500000000⟩
def contact2990 : RatBall := localContactBall tau2990 center2990
def work2990 : RoundedTauEval :=
  evalTau precision tau2990 contact2990 logTwoBall

theorem center_sq2990 : (center2990.re : ℝ)^2 +
    (center2990.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2990]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2990 : work2990.theta.ok = true ∧
    work2990.jac.invOK = true ∧ acceptsUnitSq work2990.out = true := by decide +kernel

def cell2990 : CellCertificate where
  tauBall := tau2990
  contactCenter := center2990
  contactBall := contact2990
  work := work2990
  center_sq := center_sq2990
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2990.1
  jac_ok := checks2990.2.1
  accepted := checks2990.2.2

def tau2991 : RatBall :=
  ⟨⟨41/640, -247/640⟩, 3/1280⟩
def center2991 : GaussianRat :=
  ⟨52366871/1000000000, -70290053/250000000⟩
def contact2991 : RatBall := localContactBall tau2991 center2991
def work2991 : RoundedTauEval :=
  evalTau precision tau2991 contact2991 logTwoBall

theorem center_sq2991 : (center2991.re : ℝ)^2 +
    (center2991.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2991]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2991 : work2991.theta.ok = true ∧
    work2991.jac.invOK = true ∧ acceptsUnitSq work2991.out = true := by decide +kernel

def cell2991 : CellCertificate where
  tauBall := tau2991
  contactCenter := center2991
  contactBall := contact2991
  work := work2991
  center_sq := center_sq2991
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2991.1
  jac_ok := checks2991.2.1
  accepted := checks2991.2.2

def cells : List CellCertificate := [cell2984, cell2985, cell2986, cell2987, cell2988, cell2989, cell2990, cell2991]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373

end


