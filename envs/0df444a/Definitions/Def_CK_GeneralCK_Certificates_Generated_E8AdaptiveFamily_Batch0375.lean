-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0375
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0375
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:14:15.038035+00:00
-- url     : https://prove2.me/theorems/00be5045-739a-4c66-8524-8540d222eba6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0375.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3000 : RatBall :=
  ⟨⟨47/640, -243/640⟩, 3/1280⟩
def center3000 : GaussianRat :=
  ⟨59632267/1000000000, -137808407/500000000⟩
def contact3000 : RatBall := localContactBall tau3000 center3000
def work3000 : RoundedTauEval :=
  evalTau precision tau3000 contact3000 logTwoBall

theorem center_sq3000 : (center3000.re : ℝ)^2 +
    (center3000.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3000 : work3000.theta.ok = true ∧
    work3000.jac.invOK = true ∧ acceptsUnitSq work3000.out = true := by decide +kernel

def cell3000 : CellCertificate where
  tauBall := tau3000
  contactCenter := center3000
  contactBall := contact3000
  work := work3000
  center_sq := center_sq3000
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3000.1
  jac_ok := checks3000.2.1
  accepted := checks3000.2.2

def tau3001 : RatBall :=
  ⟨⟨9/128, -241/640⟩, 3/1280⟩
def center3001 : GaussianRat :=
  ⟨11390081/200000000, -136632679/500000000⟩
def contact3001 : RatBall := localContactBall tau3001 center3001
def work3001 : RoundedTauEval :=
  evalTau precision tau3001 contact3001 logTwoBall

theorem center_sq3001 : (center3001.re : ℝ)^2 +
    (center3001.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3001]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3001 : work3001.theta.ok = true ∧
    work3001.jac.invOK = true ∧ acceptsUnitSq work3001.out = true := by decide +kernel

def cell3001 : CellCertificate where
  tauBall := tau3001
  contactCenter := center3001
  contactBall := contact3001
  work := work3001
  center_sq := center_sq3001
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3001.1
  jac_ok := checks3001.2.1
  accepted := checks3001.2.2

def tau3002 : RatBall :=
  ⟨⟨47/640, -241/640⟩, 3/1280⟩
def center3002 : GaussianRat :=
  ⟨59463601/1000000000, -273101301/1000000000⟩
def contact3002 : RatBall := localContactBall tau3002 center3002
def work3002 : RoundedTauEval :=
  evalTau precision tau3002 contact3002 logTwoBall

theorem center_sq3002 : (center3002.re : ℝ)^2 +
    (center3002.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3002]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3002 : work3002.theta.ok = true ∧
    work3002.jac.invOK = true ∧ acceptsUnitSq work3002.out = true := by decide +kernel

def cell3002 : CellCertificate where
  tauBall := tau3002
  contactCenter := center3002
  contactBall := contact3002
  work := work3002
  center_sq := center_sq3002
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3002.1
  jac_ok := checks3002.2.1
  accepted := checks3002.2.2

def tau3003 : RatBall :=
  ⟨⟨49/640, -251/640⟩, 3/1280⟩
def center3003 : GaussianRat :=
  ⟨6287709/100000000, -142783229/500000000⟩
def contact3003 : RatBall := localContactBall tau3003 center3003
def work3003 : RoundedTauEval :=
  evalTau precision tau3003 contact3003 logTwoBall

theorem center_sq3003 : (center3003.re : ℝ)^2 +
    (center3003.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3003]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3003 : work3003.theta.ok = true ∧
    work3003.jac.invOK = true ∧ acceptsUnitSq work3003.out = true := by decide +kernel

def cell3003 : CellCertificate where
  tauBall := tau3003
  contactCenter := center3003
  contactBall := contact3003
  work := work3003
  center_sq := center_sq3003
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3003.1
  jac_ok := checks3003.2.1
  accepted := checks3003.2.2

def tau3004 : RatBall :=
  ⟨⟨51/640, -251/640⟩, 3/1280⟩
def center3004 : GaussianRat :=
  ⟨65420927/1000000000, -285375989/1000000000⟩
def contact3004 : RatBall := localContactBall tau3004 center3004
def work3004 : RoundedTauEval :=
  evalTau precision tau3004 contact3004 logTwoBall

theorem center_sq3004 : (center3004.re : ℝ)^2 +
    (center3004.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3004]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3004 : work3004.theta.ok = true ∧
    work3004.jac.invOK = true ∧ acceptsUnitSq work3004.out = true := by decide +kernel

def cell3004 : CellCertificate where
  tauBall := tau3004
  contactCenter := center3004
  contactBall := contact3004
  work := work3004
  center_sq := center_sq3004
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3004.1
  jac_ok := checks3004.2.1
  accepted := checks3004.2.2

def tau3005 : RatBall :=
  ⟨⟨49/640, -249/640⟩, 3/1280⟩
def center3005 : GaussianRat :=
  ⟨62691561/1000000000, -141512483/500000000⟩
def contact3005 : RatBall := localContactBall tau3005 center3005
def work3005 : RoundedTauEval :=
  evalTau precision tau3005 contact3005 logTwoBall

theorem center_sq3005 : (center3005.re : ℝ)^2 +
    (center3005.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3005]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3005 : work3005.theta.ok = true ∧
    work3005.jac.invOK = true ∧ acceptsUnitSq work3005.out = true := by decide +kernel

def cell3005 : CellCertificate where
  tauBall := tau3005
  contactCenter := center3005
  contactBall := contact3005
  work := work3005
  center_sq := center_sq3005
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3005.1
  jac_ok := checks3005.2.1
  accepted := checks3005.2.2

def tau3006 : RatBall :=
  ⟨⟨51/640, -249/640⟩, 3/1280⟩
def center3006 : GaussianRat :=
  ⟨13045627/200000000, -141418551/500000000⟩
def contact3006 : RatBall := localContactBall tau3006 center3006
def work3006 : RoundedTauEval :=
  evalTau precision tau3006 contact3006 logTwoBall

theorem center_sq3006 : (center3006.re : ℝ)^2 +
    (center3006.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3006]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3006 : work3006.theta.ok = true ∧
    work3006.jac.invOK = true ∧ acceptsUnitSq work3006.out = true := by decide +kernel

def cell3006 : CellCertificate where
  tauBall := tau3006
  contactCenter := center3006
  contactBall := contact3006
  work := work3006
  center_sq := center_sq3006
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3006.1
  jac_ok := checks3006.2.1
  accepted := checks3006.2.2

def tau3007 : RatBall :=
  ⟨⟨53/640, -251/640⟩, 3/1280⟩
def center3007 : GaussianRat :=
  ⟨67962093/1000000000, -285178227/1000000000⟩
def contact3007 : RatBall := localContactBall tau3007 center3007
def work3007 : RoundedTauEval :=
  evalTau precision tau3007 contact3007 logTwoBall

theorem center_sq3007 : (center3007.re : ℝ)^2 +
    (center3007.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3007]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3007 : work3007.theta.ok = true ∧
    work3007.jac.invOK = true ∧ acceptsUnitSq work3007.out = true := by decide +kernel

def cell3007 : CellCertificate where
  tauBall := tau3007
  contactCenter := center3007
  contactBall := contact3007
  work := work3007
  center_sq := center_sq3007
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3007.1
  jac_ok := checks3007.2.1
  accepted := checks3007.2.2

def cells : List CellCertificate := [cell3000, cell3001, cell3002, cell3003, cell3004, cell3005, cell3006, cell3007]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375

end


