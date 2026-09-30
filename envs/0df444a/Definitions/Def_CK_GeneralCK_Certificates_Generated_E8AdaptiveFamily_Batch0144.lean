-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0144
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0144
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:33.55498+00:00
-- url     : https://prove2.me/theorems/af0fc57d-66ac-42f6-8019-a40f408e11a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0144.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1152 : RatBall :=
  ⟨⟨7/32, 33/160⟩, 3/320⟩
def center1152 : GaussianRat :=
  ⟨31103099/200000000, 137761833/1000000000⟩
def contact1152 : RatBall := localContactBall tau1152 center1152
def work1152 : RoundedTauEval :=
  evalTau precision tau1152 contact1152 logTwoBall

theorem center_sq1152 : (center1152.re : ℝ)^2 +
    (center1152.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1152]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1152 : work1152.theta.ok = true ∧
    work1152.jac.invOK = true ∧ acceptsUnitSq work1152.out = true := by decide +kernel

def cell1152 : CellCertificate where
  tauBall := tau1152
  contactCenter := center1152
  contactBall := contact1152
  work := work1152
  center_sq := center_sq1152
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1152.1
  jac_ok := checks1152.2.1
  accepted := checks1152.2.2

def tau1153 : RatBall :=
  ⟨⟨33/160, 7/32⟩, 3/320⟩
def center1153 : GaussianRat :=
  ⟨7386597/50000000, 7357917/50000000⟩
def contact1153 : RatBall := localContactBall tau1153 center1153
def work1153 : RoundedTauEval :=
  evalTau precision tau1153 contact1153 logTwoBall

theorem center_sq1153 : (center1153.re : ℝ)^2 +
    (center1153.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1153]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1153 : work1153.theta.ok = true ∧
    work1153.jac.invOK = true ∧ acceptsUnitSq work1153.out = true := by decide +kernel

def cell1153 : CellCertificate where
  tauBall := tau1153
  contactCenter := center1153
  contactBall := contact1153
  work := work1153
  center_sq := center_sq1153
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1153.1
  jac_ok := checks1153.2.1
  accepted := checks1153.2.2

def tau1154 : RatBall :=
  ⟨⟨7/32, 7/32⟩, 3/320⟩
def center1154 : GaussianRat :=
  ⟨78170517/500000000, 14632387/100000000⟩
def contact1154 : RatBall := localContactBall tau1154 center1154
def work1154 : RoundedTauEval :=
  evalTau precision tau1154 contact1154 logTwoBall

theorem center_sq1154 : (center1154.re : ℝ)^2 +
    (center1154.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1154]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1154 : work1154.theta.ok = true ∧
    work1154.jac.invOK = true ∧ acceptsUnitSq work1154.out = true := by decide +kernel

def cell1154 : CellCertificate where
  tauBall := tau1154
  contactCenter := center1154
  contactBall := contact1154
  work := work1154
  center_sq := center_sq1154
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1154.1
  jac_ok := checks1154.2.1
  accepted := checks1154.2.2

def tau1155 : RatBall :=
  ⟨⟨37/160, 33/160⟩, 3/320⟩
def center1155 : GaussianRat :=
  ⟨164030831/1000000000, 3423667/25000000⟩
def contact1155 : RatBall := localContactBall tau1155 center1155
def work1155 : RoundedTauEval :=
  evalTau precision tau1155 contact1155 logTwoBall

theorem center_sq1155 : (center1155.re : ℝ)^2 +
    (center1155.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1155]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1155 : work1155.theta.ok = true ∧
    work1155.jac.invOK = true ∧ acceptsUnitSq work1155.out = true := by decide +kernel

def cell1155 : CellCertificate where
  tauBall := tau1155
  contactCenter := center1155
  contactBall := contact1155
  work := work1155
  center_sq := center_sq1155
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1155.1
  jac_ok := checks1155.2.1
  accepted := checks1155.2.2

def tau1156 : RatBall :=
  ⟨⟨39/160, 33/160⟩, 3/320⟩
def center1156 : GaussianRat :=
  ⟨172488051/1000000000, 136096987/1000000000⟩
def contact1156 : RatBall := localContactBall tau1156 center1156
def work1156 : RoundedTauEval :=
  evalTau precision tau1156 contact1156 logTwoBall

theorem center_sq1156 : (center1156.re : ℝ)^2 +
    (center1156.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1156]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1156 : work1156.theta.ok = true ∧
    work1156.jac.invOK = true ∧ acceptsUnitSq work1156.out = true := by decide +kernel

def cell1156 : CellCertificate where
  tauBall := tau1156
  contactCenter := center1156
  contactBall := contact1156
  work := work1156
  center_sq := center_sq1156
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1156.1
  jac_ok := checks1156.2.1
  accepted := checks1156.2.2

def tau1157 : RatBall :=
  ⟨⟨37/160, 7/32⟩, 3/320⟩
def center1157 : GaussianRat :=
  ⟨164892819/1000000000, 29090197/200000000⟩
def contact1157 : RatBall := localContactBall tau1157 center1157
def work1157 : RoundedTauEval :=
  evalTau precision tau1157 contact1157 logTwoBall

theorem center_sq1157 : (center1157.re : ℝ)^2 +
    (center1157.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1157]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1157 : work1157.theta.ok = true ∧
    work1157.jac.invOK = true ∧ acceptsUnitSq work1157.out = true := by decide +kernel

def cell1157 : CellCertificate where
  tauBall := tau1157
  contactCenter := center1157
  contactBall := contact1157
  work := work1157
  center_sq := center_sq1157
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1157.1
  jac_ok := checks1157.2.1
  accepted := checks1157.2.2

def tau1158 : RatBall :=
  ⟨⟨39/160, 7/32⟩, 3/320⟩
def center1158 : GaussianRat :=
  ⟨173384937/1000000000, 144541281/1000000000⟩
def contact1158 : RatBall := localContactBall tau1158 center1158
def work1158 : RoundedTauEval :=
  evalTau precision tau1158 contact1158 logTwoBall

theorem center_sq1158 : (center1158.re : ℝ)^2 +
    (center1158.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1158]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1158 : work1158.theta.ok = true ∧
    work1158.jac.invOK = true ∧ acceptsUnitSq work1158.out = true := by decide +kernel

def cell1158 : CellCertificate where
  tauBall := tau1158
  contactCenter := center1158
  contactBall := contact1158
  work := work1158
  center_sq := center_sq1158
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1158.1
  jac_ok := checks1158.2.1
  accepted := checks1158.2.2

def tau1159 : RatBall :=
  ⟨⟨33/160, 37/160⟩, 3/320⟩
def center1159 : GaussianRat :=
  ⟨148574359/1000000000, 31163137/200000000⟩
def contact1159 : RatBall := localContactBall tau1159 center1159
def work1159 : RoundedTauEval :=
  evalTau precision tau1159 contact1159 logTwoBall

theorem center_sq1159 : (center1159.re : ℝ)^2 +
    (center1159.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1159]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1159 : work1159.theta.ok = true ∧
    work1159.jac.invOK = true ∧ acceptsUnitSq work1159.out = true := by decide +kernel

def cell1159 : CellCertificate where
  tauBall := tau1159
  contactCenter := center1159
  contactBall := contact1159
  work := work1159
  center_sq := center_sq1159
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1159.1
  jac_ok := checks1159.2.1
  accepted := checks1159.2.2

def cells : List CellCertificate := [cell1152, cell1153, cell1154, cell1155, cell1156, cell1157, cell1158, cell1159]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144

end


