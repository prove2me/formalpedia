-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0011
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0011
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:14:35.441055+00:00
-- url     : https://prove2.me/theorems/bd8ceca9-693a-43ef-a3ff-b334f68ef0e4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0011.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0088 : RatBall :=
  ⟨⟨-27/80, -1/16⟩, 3/160⟩
def center0088 : GaussianRat :=
  ⟨-22606221/100000000, -4844151/125000000⟩
def contact0088 : RatBall := localContactBall tau0088 center0088
def work0088 : RoundedTauEval :=
  evalTau precision tau0088 contact0088 logTwoBall

theorem center_sq0088 : (center0088.re : ℝ)^2 +
    (center0088.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0088]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0088 : work0088.theta.ok = true ∧
    work0088.jac.invOK = true ∧ acceptsUnitSq work0088.out = true := by decide +kernel

def cell0088 : CellCertificate where
  tauBall := tau0088
  contactCenter := center0088
  contactBall := contact0088
  work := work0088
  center_sq := center_sq0088
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0088.1
  jac_ok := checks0088.2.1
  accepted := checks0088.2.2

def tau0089 : RatBall :=
  ⟨⟨-5/16, -1/16⟩, 3/160⟩
def center0089 : GaussianRat :=
  ⟨-26302089/125000000, -3935289/100000000⟩
def contact0089 : RatBall := localContactBall tau0089 center0089
def work0089 : RoundedTauEval :=
  evalTau precision tau0089 contact0089 logTwoBall

theorem center_sq0089 : (center0089.re : ℝ)^2 +
    (center0089.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0089]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0089 : work0089.theta.ok = true ∧
    work0089.jac.invOK = true ∧ acceptsUnitSq work0089.out = true := by decide +kernel

def cell0089 : CellCertificate where
  tauBall := tau0089
  contactCenter := center0089
  contactBall := contact0089
  work := work0089
  center_sq := center_sq0089
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0089.1
  jac_ok := checks0089.2.1
  accepted := checks0089.2.2

def tau0090 : RatBall :=
  ⟨⟨-29/80, -3/80⟩, 3/160⟩
def center0090 : GaussianRat :=
  ⟨-120475049/500000000, -4573419/200000000⟩
def contact0090 : RatBall := localContactBall tau0090 center0090
def work0090 : RoundedTauEval :=
  evalTau precision tau0090 contact0090 logTwoBall

theorem center_sq0090 : (center0090.re : ℝ)^2 +
    (center0090.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0090]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0090 : work0090.theta.ok = true ∧
    work0090.jac.invOK = true ∧ acceptsUnitSq work0090.out = true := by decide +kernel

def cell0090 : CellCertificate where
  tauBall := tau0090
  contactCenter := center0090
  contactBall := contact0090
  work := work0090
  center_sq := center_sq0090
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0090.1
  jac_ok := checks0090.2.1
  accepted := checks0090.2.2

def tau0091 : RatBall :=
  ⟨⟨-31/80, -1/80⟩, 3/160⟩
def center0091 : GaussianRat :=
  ⟨-255809887/1000000000, -749167/100000000⟩
def contact0091 : RatBall := localContactBall tau0091 center0091
def work0091 : RoundedTauEval :=
  evalTau precision tau0091 contact0091 logTwoBall

theorem center_sq0091 : (center0091.re : ℝ)^2 +
    (center0091.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0091]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0091 : work0091.theta.ok = true ∧
    work0091.jac.invOK = true ∧ acceptsUnitSq work0091.out = true := by decide +kernel

def cell0091 : CellCertificate where
  tauBall := tau0091
  contactCenter := center0091
  contactBall := contact0091
  work := work0091
  center_sq := center_sq0091
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0091.1
  jac_ok := checks0091.2.1
  accepted := checks0091.2.2

def tau0092 : RatBall :=
  ⟨⟨-29/80, -1/80⟩, 3/160⟩
def center0092 : GaussianRat :=
  ⟨-240695961/1000000000, -1905207/250000000⟩
def contact0092 : RatBall := localContactBall tau0092 center0092
def work0092 : RoundedTauEval :=
  evalTau precision tau0092 contact0092 logTwoBall

theorem center_sq0092 : (center0092.re : ℝ)^2 +
    (center0092.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0092]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0092 : work0092.theta.ok = true ∧
    work0092.jac.invOK = true ∧ acceptsUnitSq work0092.out = true := by decide +kernel

def cell0092 : CellCertificate where
  tauBall := tau0092
  contactCenter := center0092
  contactBall := contact0092
  work := work0092
  center_sq := center_sq0092
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0092.1
  jac_ok := checks0092.2.1
  accepted := checks0092.2.2

def tau0093 : RatBall :=
  ⟨⟨-27/80, -3/80⟩, 3/160⟩
def center0093 : GaussianRat :=
  ⟨-225572371/1000000000, -4648277/200000000⟩
def contact0093 : RatBall := localContactBall tau0093 center0093
def work0093 : RoundedTauEval :=
  evalTau precision tau0093 contact0093 logTwoBall

theorem center_sq0093 : (center0093.re : ℝ)^2 +
    (center0093.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0093]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0093 : work0093.theta.ok = true ∧
    work0093.jac.invOK = true ∧ acceptsUnitSq work0093.out = true := by decide +kernel

def cell0093 : CellCertificate where
  tauBall := tau0093
  contactCenter := center0093
  contactBall := contact0093
  work := work0093
  center_sq := center_sq0093
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0093.1
  jac_ok := checks0093.2.1
  accepted := checks0093.2.2

def tau0094 : RatBall :=
  ⟨⟨-5/16, -3/80⟩, 3/160⟩
def center0094 : GaussianRat :=
  ⟨-209949283/1000000000, -11799931/500000000⟩
def contact0094 : RatBall := localContactBall tau0094 center0094
def work0094 : RoundedTauEval :=
  evalTau precision tau0094 contact0094 logTwoBall

theorem center_sq0094 : (center0094.re : ℝ)^2 +
    (center0094.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0094]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0094 : work0094.theta.ok = true ∧
    work0094.jac.invOK = true ∧ acceptsUnitSq work0094.out = true := by decide +kernel

def cell0094 : CellCertificate where
  tauBall := tau0094
  contactCenter := center0094
  contactBall := contact0094
  work := work0094
  center_sq := center_sq0094
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0094.1
  jac_ok := checks0094.2.1
  accepted := checks0094.2.2

def tau0095 : RatBall :=
  ⟨⟨-27/80, -1/80⟩, 3/160⟩
def center0095 : GaussianRat :=
  ⟨-45065623/200000000, -7745371/1000000000⟩
def contact0095 : RatBall := localContactBall tau0095 center0095
def work0095 : RoundedTauEval :=
  evalTau precision tau0095 contact0095 logTwoBall

theorem center_sq0095 : (center0095.re : ℝ)^2 +
    (center0095.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0095]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0095 : work0095.theta.ok = true ∧
    work0095.jac.invOK = true ∧ acceptsUnitSq work0095.out = true := by decide +kernel

def cell0095 : CellCertificate where
  tauBall := tau0095
  contactCenter := center0095
  contactBall := contact0095
  work := work0095
  center_sq := center_sq0095
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0095.1
  jac_ok := checks0095.2.1
  accepted := checks0095.2.2

def cells : List CellCertificate := [cell0088, cell0089, cell0090, cell0091, cell0092, cell0093, cell0094, cell0095]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011

end


