-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0038_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0038_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:02:29.888185+00:00
-- url     : https://prove2.me/theorems/f35bcf3e-59c3-4d10-ac47-b1faf3640899
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0038 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0304 : RatBall :=
  ⟨⟨31/80, 1/80⟩, 3/160⟩
def center0304 : GaussianRat :=
  ⟨255809887/1000000000, 749167/100000000⟩
def contact0304 : RatBall := localContactBall tau0304 center0304
def work0304 : RoundedTauEval :=
  evalTau precision tau0304 contact0304 logTwoBall

theorem center_sq0304 : (center0304.re : ℝ)^2 +
    (center0304.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0304]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0304 : work0304.theta.ok = true ∧
    work0304.jac.invOK = true ∧ acceptsUnitSq work0304.out = true := by decide +kernel

def cell0304 : CellCertificate where
  tauBall := tau0304
  contactCenter := center0304
  contactBall := contact0304
  work := work0304
  center_sq := center_sq0304
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0304.1
  jac_ok := checks0304.2.1
  accepted := checks0304.2.2

def tau0305 : RatBall :=
  ⟨⟨29/80, 3/80⟩, 3/160⟩
def center0305 : GaussianRat :=
  ⟨120475049/500000000, 4573419/200000000⟩
def contact0305 : RatBall := localContactBall tau0305 center0305
def work0305 : RoundedTauEval :=
  evalTau precision tau0305 contact0305 logTwoBall

theorem center_sq0305 : (center0305.re : ℝ)^2 +
    (center0305.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0305]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0305 : work0305.theta.ok = true ∧
    work0305.jac.invOK = true ∧ acceptsUnitSq work0305.out = true := by decide +kernel

def cell0305 : CellCertificate where
  tauBall := tau0305
  contactCenter := center0305
  contactBall := contact0305
  work := work0305
  center_sq := center_sq0305
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0305.1
  jac_ok := checks0305.2.1
  accepted := checks0305.2.2

def tau0306 : RatBall :=
  ⟨⟨5/16, 1/16⟩, 3/160⟩
def center0306 : GaussianRat :=
  ⟨26302089/125000000, 3935289/100000000⟩
def contact0306 : RatBall := localContactBall tau0306 center0306
def work0306 : RoundedTauEval :=
  evalTau precision tau0306 contact0306 logTwoBall

theorem center_sq0306 : (center0306.re : ℝ)^2 +
    (center0306.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0306]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0306 : work0306.theta.ok = true ∧
    work0306.jac.invOK = true ∧ acceptsUnitSq work0306.out = true := by decide +kernel

def cell0306 : CellCertificate where
  tauBall := tau0306
  contactCenter := center0306
  contactBall := contact0306
  work := work0306
  center_sq := center_sq0306
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0306.1
  jac_ok := checks0306.2.1
  accepted := checks0306.2.2

def tau0307 : RatBall :=
  ⟨⟨27/80, 1/16⟩, 3/160⟩
def center0307 : GaussianRat :=
  ⟨22606221/100000000, 4844151/125000000⟩
def contact0307 : RatBall := localContactBall tau0307 center0307
def work0307 : RoundedTauEval :=
  evalTau precision tau0307 contact0307 logTwoBall

theorem center_sq0307 : (center0307.re : ℝ)^2 +
    (center0307.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0307]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0307 : work0307.theta.ok = true ∧
    work0307.jac.invOK = true ∧ acceptsUnitSq work0307.out = true := by decide +kernel

def cell0307 : CellCertificate where
  tauBall := tau0307
  contactCenter := center0307
  contactBall := contact0307
  work := work0307
  center_sq := center_sq0307
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0307.1
  jac_ok := checks0307.2.1
  accepted := checks0307.2.2

def tau0308 : RatBall :=
  ⟨⟨5/16, 7/80⟩, 3/160⟩
def center0308 : GaussianRat :=
  ⟨211121197/1000000000, 55135609/1000000000⟩
def contact0308 : RatBall := localContactBall tau0308 center0308
def work0308 : RoundedTauEval :=
  evalTau precision tau0308 contact0308 logTwoBall

theorem center_sq0308 : (center0308.re : ℝ)^2 +
    (center0308.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0308 : work0308.theta.ok = true ∧
    work0308.jac.invOK = true ∧ acceptsUnitSq work0308.out = true := by decide +kernel

def cell0308 : CellCertificate where
  tauBall := tau0308
  contactCenter := center0308
  contactBall := contact0308
  work := work0308
  center_sq := center_sq0308
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0308.1
  jac_ok := checks0308.2.1
  accepted := checks0308.2.2

def tau0309 : RatBall :=
  ⟨⟨27/80, 7/80⟩, 3/160⟩
def center0309 : GaussianRat :=
  ⟨14175019/62500000, 54291363/1000000000⟩
def contact0309 : RatBall := localContactBall tau0309 center0309
def work0309 : RoundedTauEval :=
  evalTau precision tau0309 contact0309 logTwoBall

theorem center_sq0309 : (center0309.re : ℝ)^2 +
    (center0309.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0309]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0309 : work0309.theta.ok = true ∧
    work0309.jac.invOK = true ∧ acceptsUnitSq work0309.out = true := by decide +kernel

def cell0309 : CellCertificate where
  tauBall := tau0309
  contactCenter := center0309
  contactBall := contact0309
  work := work0309
  center_sq := center_sq0309
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0309.1
  jac_ok := checks0309.2.1
  accepted := checks0309.2.2

def tau0310 : RatBall :=
  ⟨⟨29/80, 1/16⟩, 3/160⟩
def center0310 : GaussianRat :=
  ⟨241459683/1000000000, 9531797/250000000⟩
def contact0310 : RatBall := localContactBall tau0310 center0310
def work0310 : RoundedTauEval :=
  evalTau precision tau0310 contact0310 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038


