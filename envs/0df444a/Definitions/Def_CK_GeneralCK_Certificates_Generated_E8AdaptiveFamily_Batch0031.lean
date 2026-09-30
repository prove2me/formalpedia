-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0031
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0031
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:48:13.556665+00:00
-- url     : https://prove2.me/theorems/ffd95a21-7130-42d5-9142-a31c5b77056b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0031.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0248 : RatBall :=
  ⟨⟨-1/16, 13/80⟩, 3/160⟩
def center0248 : GaussianRat :=
  ⟨-44475471/1000000000, 14150393/125000000⟩
def contact0248 : RatBall := localContactBall tau0248 center0248
def work0248 : RoundedTauEval :=
  evalTau precision tau0248 contact0248 logTwoBall

theorem center_sq0248 : (center0248.re : ℝ)^2 +
    (center0248.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0248 : work0248.theta.ok = true ∧
    work0248.jac.invOK = true ∧ acceptsUnitSq work0248.out = true := by decide +kernel

def cell0248 : CellCertificate where
  tauBall := tau0248
  contactCenter := center0248
  contactBall := contact0248
  work := work0248
  center_sq := center_sq0248
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0248.1
  jac_ok := checks0248.2.1
  accepted := checks0248.2.2

def tau0249 : RatBall :=
  ⟨⟨-7/80, 3/16⟩, 3/160⟩
def center0249 : GaussianRat :=
  ⟨-6275219/100000000, 65240079/500000000⟩
def contact0249 : RatBall := localContactBall tau0249 center0249
def work0249 : RoundedTauEval :=
  evalTau precision tau0249 contact0249 logTwoBall

theorem center_sq0249 : (center0249.re : ℝ)^2 +
    (center0249.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0249]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0249 : work0249.theta.ok = true ∧
    work0249.jac.invOK = true ∧ acceptsUnitSq work0249.out = true := by decide +kernel

def cell0249 : CellCertificate where
  tauBall := tau0249
  contactCenter := center0249
  contactBall := contact0249
  work := work0249
  center_sq := center_sq0249
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0249.1
  jac_ok := checks0249.2.1
  accepted := checks0249.2.2

def tau0250 : RatBall :=
  ⟨⟨-1/16, 3/16⟩, 3/160⟩
def center0250 : GaussianRat :=
  ⟨-22445977/500000000, 131018253/1000000000⟩
def contact0250 : RatBall := localContactBall tau0250 center0250
def work0250 : RoundedTauEval :=
  evalTau precision tau0250 contact0250 logTwoBall

theorem center_sq0250 : (center0250.re : ℝ)^2 +
    (center0250.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0250 : work0250.theta.ok = true ∧
    work0250.jac.invOK = true ∧ acceptsUnitSq work0250.out = true := by decide +kernel

def cell0250 : CellCertificate where
  tauBall := tau0250
  contactCenter := center0250
  contactBall := contact0250
  work := work0250
  center_sq := center_sq0250
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0250.1
  jac_ok := checks0250.2.1
  accepted := checks0250.2.2

def tau0251 : RatBall :=
  ⟨⟨-3/16, 17/80⟩, 3/160⟩
def center0251 : GaussianRat :=
  ⟨-16793263/125000000, 143981719/1000000000⟩
def contact0251 : RatBall := localContactBall tau0251 center0251
def work0251 : RoundedTauEval :=
  evalTau precision tau0251 contact0251 logTwoBall

theorem center_sq0251 : (center0251.re : ℝ)^2 +
    (center0251.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0251]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0251 : work0251.theta.ok = true ∧
    work0251.jac.invOK = true ∧ acceptsUnitSq work0251.out = true := by decide +kernel

def cell0251 : CellCertificate where
  tauBall := tau0251
  contactCenter := center0251
  contactBall := contact0251
  work := work0251
  center_sq := center_sq0251
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0251.1
  jac_ok := checks0251.2.1
  accepted := checks0251.2.2

def tau0252 : RatBall :=
  ⟨⟨-13/80, 17/80⟩, 3/160⟩
def center0252 : GaussianRat :=
  ⟨-58429249/500000000, 145353777/1000000000⟩
def contact0252 : RatBall := localContactBall tau0252 center0252
def work0252 : RoundedTauEval :=
  evalTau precision tau0252 contact0252 logTwoBall

theorem center_sq0252 : (center0252.re : ℝ)^2 +
    (center0252.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0252 : work0252.theta.ok = true ∧
    work0252.jac.invOK = true ∧ acceptsUnitSq work0252.out = true := by decide +kernel

def cell0252 : CellCertificate where
  tauBall := tau0252
  contactCenter := center0252
  contactBall := contact0252
  work := work0252
  center_sq := center_sq0252
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0252.1
  jac_ok := checks0252.2.1
  accepted := checks0252.2.2

def tau0253 : RatBall :=
  ⟨⟨-11/80, 17/80⟩, 3/160⟩
def center0253 : GaussianRat :=
  ⟨-24798221/250000000, 36637923/250000000⟩
def contact0253 : RatBall := localContactBall tau0253 center0253
def work0253 : RoundedTauEval :=
  evalTau precision tau0253 contact0253 logTwoBall

theorem center_sq0253 : (center0253.re : ℝ)^2 +
    (center0253.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0253]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0253 : work0253.theta.ok = true ∧
    work0253.jac.invOK = true ∧ acceptsUnitSq work0253.out = true := by decide +kernel

def cell0253 : CellCertificate where
  tauBall := tau0253
  contactCenter := center0253
  contactBall := contact0253
  work := work0253
  center_sq := center_sq0253
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0253.1
  jac_ok := checks0253.2.1
  accepted := checks0253.2.2

def tau0254 : RatBall :=
  ⟨⟨-9/80, 17/80⟩, 3/160⟩
def center0254 : GaussianRat :=
  ⟨-4068673/50000000, 73782899/500000000⟩
def contact0254 : RatBall := localContactBall tau0254 center0254
def work0254 : RoundedTauEval :=
  evalTau precision tau0254 contact0254 logTwoBall

theorem center_sq0254 : (center0254.re : ℝ)^2 +
    (center0254.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0254]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0254 : work0254.theta.ok = true ∧
    work0254.jac.invOK = true ∧ acceptsUnitSq work0254.out = true := by decide +kernel

def cell0254 : CellCertificate where
  tauBall := tau0254
  contactCenter := center0254
  contactBall := contact0254
  work := work0254
  center_sq := center_sq0254
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0254.1
  jac_ok := checks0254.2.1
  accepted := checks0254.2.2

def tau0255 : RatBall :=
  ⟨⟨-11/80, 19/80⟩, 3/160⟩
def center0255 : GaussianRat :=
  ⟨-25094739/250000000, 82197279/500000000⟩
def contact0255 : RatBall := localContactBall tau0255 center0255
def work0255 : RoundedTauEval :=
  evalTau precision tau0255 contact0255 logTwoBall

theorem center_sq0255 : (center0255.re : ℝ)^2 +
    (center0255.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0255]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0255 : work0255.theta.ok = true ∧
    work0255.jac.invOK = true ∧ acceptsUnitSq work0255.out = true := by decide +kernel

def cell0255 : CellCertificate where
  tauBall := tau0255
  contactCenter := center0255
  contactBall := contact0255
  work := work0255
  center_sq := center_sq0255
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0255.1
  jac_ok := checks0255.2.1
  accepted := checks0255.2.2

def cells : List CellCertificate := [cell0248, cell0249, cell0250, cell0251, cell0252, cell0253, cell0254, cell0255]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031

end


