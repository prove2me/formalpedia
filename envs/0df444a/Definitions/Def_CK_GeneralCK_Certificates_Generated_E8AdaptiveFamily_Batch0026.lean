-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0026
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0026
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:42:13.777453+00:00
-- url     : https://prove2.me/theorems/b3b5d02f-c6de-4d39-b5e9-2b8964a7c585
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0026.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0208 : RatBall :=
  ⟨⟨-27/80, 7/80⟩, 3/160⟩
def center0208 : GaussianRat :=
  ⟨-14175019/62500000, 54291363/1000000000⟩
def contact0208 : RatBall := localContactBall tau0208 center0208
def work0208 : RoundedTauEval :=
  evalTau precision tau0208 contact0208 logTwoBall

theorem center_sq0208 : (center0208.re : ℝ)^2 +
    (center0208.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0208]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0208 : work0208.theta.ok = true ∧
    work0208.jac.invOK = true ∧ acceptsUnitSq work0208.out = true := by decide +kernel

def cell0208 : CellCertificate where
  tauBall := tau0208
  contactCenter := center0208
  contactBall := contact0208
  work := work0208
  center_sq := center_sq0208
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0208.1
  jac_ok := checks0208.2.1
  accepted := checks0208.2.2

def tau0209 : RatBall :=
  ⟨⟨-5/16, 7/80⟩, 3/160⟩
def center0209 : GaussianRat :=
  ⟨-211121197/1000000000, 55135609/1000000000⟩
def contact0209 : RatBall := localContactBall tau0209 center0209
def work0209 : RoundedTauEval :=
  evalTau precision tau0209 contact0209 logTwoBall

theorem center_sq0209 : (center0209.re : ℝ)^2 +
    (center0209.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0209]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0209 : work0209.theta.ok = true ∧
    work0209.jac.invOK = true ∧ acceptsUnitSq work0209.out = true := by decide +kernel

def cell0209 : CellCertificate where
  tauBall := tau0209
  contactCenter := center0209
  contactBall := contact0209
  work := work0209
  center_sq := center_sq0209
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0209.1
  jac_ok := checks0209.2.1
  accepted := checks0209.2.2

def tau0210 : RatBall :=
  ⟨⟨-23/80, 1/80⟩, 3/160⟩
def center0210 : GaussianRat :=
  ⟨-7754861/40000000, 3988989/500000000⟩
def contact0210 : RatBall := localContactBall tau0210 center0210
def work0210 : RoundedTauEval :=
  evalTau precision tau0210 contact0210 logTwoBall

theorem center_sq0210 : (center0210.re : ℝ)^2 +
    (center0210.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0210]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0210 : work0210.theta.ok = true ∧
    work0210.jac.invOK = true ∧ acceptsUnitSq work0210.out = true := by decide +kernel

def cell0210 : CellCertificate where
  tauBall := tau0210
  contactCenter := center0210
  contactBall := contact0210
  work := work0210
  center_sq := center_sq0210
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0210.1
  jac_ok := checks0210.2.1
  accepted := checks0210.2.2

def tau0211 : RatBall :=
  ⟨⟨-21/80, 1/80⟩, 3/160⟩
def center0211 : GaussianRat :=
  ⟨-4445163/25000000, 8084719/1000000000⟩
def contact0211 : RatBall := localContactBall tau0211 center0211
def work0211 : RoundedTauEval :=
  evalTau precision tau0211 contact0211 logTwoBall

theorem center_sq0211 : (center0211.re : ℝ)^2 +
    (center0211.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0211]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0211 : work0211.theta.ok = true ∧
    work0211.jac.invOK = true ∧ acceptsUnitSq work0211.out = true := by decide +kernel

def cell0211 : CellCertificate where
  tauBall := tau0211
  contactCenter := center0211
  contactBall := contact0211
  work := work0211
  center_sq := center_sq0211
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0211.1
  jac_ok := checks0211.2.1
  accepted := checks0211.2.2

def tau0212 : RatBall :=
  ⟨⟨-23/80, 3/80⟩, 3/160⟩
def center0212 : GaussianRat :=
  ⟨-4852301/25000000, 23940531/1000000000⟩
def contact0212 : RatBall := localContactBall tau0212 center0212
def work0212 : RoundedTauEval :=
  evalTau precision tau0212 contact0212 logTwoBall

theorem center_sq0212 : (center0212.re : ℝ)^2 +
    (center0212.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0212]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0212 : work0212.theta.ok = true ∧
    work0212.jac.invOK = true ∧ acceptsUnitSq work0212.out = true := by decide +kernel

def cell0212 : CellCertificate where
  tauBall := tau0212
  contactCenter := center0212
  contactBall := contact0212
  work := work0212
  center_sq := center_sq0212
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0212.1
  jac_ok := checks0212.2.1
  accepted := checks0212.2.2

def tau0213 : RatBall :=
  ⟨⟨-21/80, 3/80⟩, 3/160⟩
def center0213 : GaussianRat :=
  ⟨-89006593/500000000, 4852281/200000000⟩
def contact0213 : RatBall := localContactBall tau0213 center0213
def work0213 : RoundedTauEval :=
  evalTau precision tau0213 contact0213 logTwoBall

theorem center_sq0213 : (center0213.re : ℝ)^2 +
    (center0213.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0213]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0213 : work0213.theta.ok = true ∧
    work0213.jac.invOK = true ∧ acceptsUnitSq work0213.out = true := by decide +kernel

def cell0213 : CellCertificate where
  tauBall := tau0213
  contactCenter := center0213
  contactBall := contact0213
  work := work0213
  center_sq := center_sq0213
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0213.1
  jac_ok := checks0213.2.1
  accepted := checks0213.2.2

def tau0214 : RatBall :=
  ⟨⟨-23/80, 1/16⟩, 3/160⟩
def center0214 : GaussianRat :=
  ⟨-194534387/1000000000, 7984577/200000000⟩
def contact0214 : RatBall := localContactBall tau0214 center0214
def work0214 : RoundedTauEval :=
  evalTau precision tau0214 contact0214 logTwoBall

theorem center_sq0214 : (center0214.re : ℝ)^2 +
    (center0214.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0214]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0214 : work0214.theta.ok = true ∧
    work0214.jac.invOK = true ∧ acceptsUnitSq work0214.out = true := by decide +kernel

def cell0214 : CellCertificate where
  tauBall := tau0214
  contactCenter := center0214
  contactBall := contact0214
  work := work0214
  center_sq := center_sq0214
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0214.1
  jac_ok := checks0214.2.1
  accepted := checks0214.2.2

def tau0215 : RatBall :=
  ⟨⟨-21/80, 1/16⟩, 3/160⟩
def center0215 : GaussianRat :=
  ⟨-35685561/200000000, 40459851/1000000000⟩
def contact0215 : RatBall := localContactBall tau0215 center0215
def work0215 : RoundedTauEval :=
  evalTau precision tau0215 contact0215 logTwoBall

theorem center_sq0215 : (center0215.re : ℝ)^2 +
    (center0215.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0215]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0215 : work0215.theta.ok = true ∧
    work0215.jac.invOK = true ∧ acceptsUnitSq work0215.out = true := by decide +kernel

def cell0215 : CellCertificate where
  tauBall := tau0215
  contactCenter := center0215
  contactBall := contact0215
  work := work0215
  center_sq := center_sq0215
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0215.1
  jac_ok := checks0215.2.1
  accepted := checks0215.2.2

def cells : List CellCertificate := [cell0208, cell0209, cell0210, cell0211, cell0212, cell0213, cell0214, cell0215]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026

end


