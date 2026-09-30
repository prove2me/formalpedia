-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0327
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0327
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:55:09.937638+00:00
-- url     : https://prove2.me/theorems/1c96fbe7-617d-4795-aa3b-9131f84c0d68
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0327.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2616 : RatBall :=
  ⟨⟨-109/640, -227/640⟩, 3/1280⟩
def center2616 : GaussianRat :=
  ⟨-133380131/1000000000, -248126483/1000000000⟩
def contact2616 : RatBall := localContactBall tau2616 center2616
def work2616 : RoundedTauEval :=
  evalTau precision tau2616 contact2616 logTwoBall

theorem center_sq2616 : (center2616.re : ℝ)^2 +
    (center2616.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2616]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2616 : work2616.theta.ok = true ∧
    work2616.jac.invOK = true ∧ acceptsUnitSq work2616.out = true := by decide +kernel

def cell2616 : CellCertificate where
  tauBall := tau2616
  contactCenter := center2616
  contactBall := contact2616
  work := work2616
  center_sq := center_sq2616
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2616.1
  jac_ok := checks2616.2.1
  accepted := checks2616.2.2

def tau2617 : RatBall :=
  ⟨⟨-111/640, -45/128⟩, 3/1280⟩
def center2617 : GaussianRat :=
  ⟨-67704553/500000000, -6135977/25000000⟩
def contact2617 : RatBall := localContactBall tau2617 center2617
def work2617 : RoundedTauEval :=
  evalTau precision tau2617 contact2617 logTwoBall

theorem center_sq2617 : (center2617.re : ℝ)^2 +
    (center2617.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2617]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2617 : work2617.theta.ok = true ∧
    work2617.jac.invOK = true ∧ acceptsUnitSq work2617.out = true := by decide +kernel

def cell2617 : CellCertificate where
  tauBall := tau2617
  contactCenter := center2617
  contactBall := contact2617
  work := work2617
  center_sq := center_sq2617
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2617.1
  jac_ok := checks2617.2.1
  accepted := checks2617.2.2

def tau2618 : RatBall :=
  ⟨⟨-109/640, -45/128⟩, 3/1280⟩
def center2618 : GaussianRat :=
  ⟨-26610681/200000000, -245766093/1000000000⟩
def contact2618 : RatBall := localContactBall tau2618 center2618
def work2618 : RoundedTauEval :=
  evalTau precision tau2618 contact2618 logTwoBall

theorem center_sq2618 : (center2618.re : ℝ)^2 +
    (center2618.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2618]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2618 : work2618.theta.ok = true ∧
    work2618.jac.invOK = true ∧ acceptsUnitSq work2618.out = true := by decide +kernel

def cell2618 : CellCertificate where
  tauBall := tau2618
  contactCenter := center2618
  contactBall := contact2618
  work := work2618
  center_sq := center_sq2618
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2618.1
  jac_ok := checks2618.2.1
  accepted := checks2618.2.2

def tau2619 : RatBall :=
  ⟨⟨-103/640, -231/640⟩, 3/1280⟩
def center2619 : GaussianRat :=
  ⟨-63453799/500000000, -253852567/1000000000⟩
def contact2619 : RatBall := localContactBall tau2619 center2619
def work2619 : RoundedTauEval :=
  evalTau precision tau2619 contact2619 logTwoBall

theorem center_sq2619 : (center2619.re : ℝ)^2 +
    (center2619.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2619]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2619 : work2619.theta.ok = true ∧
    work2619.jac.invOK = true ∧ acceptsUnitSq work2619.out = true := by decide +kernel

def cell2619 : CellCertificate where
  tauBall := tau2619
  contactCenter := center2619
  contactBall := contact2619
  work := work2619
  center_sq := center_sq2619
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2619.1
  jac_ok := checks2619.2.1
  accepted := checks2619.2.2

def tau2620 : RatBall :=
  ⟨⟨-101/640, -231/640⟩, 3/1280⟩
def center2620 : GaussianRat :=
  ⟨-15564887/125000000, -254172071/1000000000⟩
def contact2620 : RatBall := localContactBall tau2620 center2620
def work2620 : RoundedTauEval :=
  evalTau precision tau2620 contact2620 logTwoBall

theorem center_sq2620 : (center2620.re : ℝ)^2 +
    (center2620.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2620]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2620 : work2620.theta.ok = true ∧
    work2620.jac.invOK = true ∧ acceptsUnitSq work2620.out = true := by decide +kernel

def cell2620 : CellCertificate where
  tauBall := tau2620
  contactCenter := center2620
  contactBall := contact2620
  work := work2620
  center_sq := center_sq2620
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2620.1
  jac_ok := checks2620.2.1
  accepted := checks2620.2.2

def tau2621 : RatBall :=
  ⟨⟨-103/640, -229/640⟩, 3/1280⟩
def center2621 : GaussianRat :=
  ⟨-126587587/1000000000, -125734431/500000000⟩
def contact2621 : RatBall := localContactBall tau2621 center2621
def work2621 : RoundedTauEval :=
  evalTau precision tau2621 contact2621 logTwoBall

theorem center_sq2621 : (center2621.re : ℝ)^2 +
    (center2621.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2621]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2621 : work2621.theta.ok = true ∧
    work2621.jac.invOK = true ∧ acceptsUnitSq work2621.out = true := by decide +kernel

def cell2621 : CellCertificate where
  tauBall := tau2621
  contactCenter := center2621
  contactBall := contact2621
  work := work2621
  center_sq := center_sq2621
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2621.1
  jac_ok := checks2621.2.1
  accepted := checks2621.2.2

def tau2622 : RatBall :=
  ⟨⟨-101/640, -229/640⟩, 3/1280⟩
def center2622 : GaussianRat :=
  ⟨-62102193/500000000, -7868253/31250000⟩
def contact2622 : RatBall := localContactBall tau2622 center2622
def work2622 : RoundedTauEval :=
  evalTau precision tau2622 contact2622 logTwoBall

theorem center_sq2622 : (center2622.re : ℝ)^2 +
    (center2622.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2622]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2622 : work2622.theta.ok = true ∧
    work2622.jac.invOK = true ∧ acceptsUnitSq work2622.out = true := by decide +kernel

def cell2622 : CellCertificate where
  tauBall := tau2622
  contactCenter := center2622
  contactBall := contact2622
  work := work2622
  center_sq := center_sq2622
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2622.1
  jac_ok := checks2622.2.1
  accepted := checks2622.2.2

def tau2623 : RatBall :=
  ⟨⟨-99/640, -231/640⟩, 3/1280⟩
def center2623 : GaussianRat :=
  ⟨-122126333/1000000000, -127243109/500000000⟩
def contact2623 : RatBall := localContactBall tau2623 center2623
def work2623 : RoundedTauEval :=
  evalTau precision tau2623 contact2623 logTwoBall

theorem center_sq2623 : (center2623.re : ℝ)^2 +
    (center2623.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2623]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2623 : work2623.theta.ok = true ∧
    work2623.jac.invOK = true ∧ acceptsUnitSq work2623.out = true := by decide +kernel

def cell2623 : CellCertificate where
  tauBall := tau2623
  contactCenter := center2623
  contactBall := contact2623
  work := work2623
  center_sq := center_sq2623
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2623.1
  jac_ok := checks2623.2.1
  accepted := checks2623.2.2

def cells : List CellCertificate := [cell2616, cell2617, cell2618, cell2619, cell2620, cell2621, cell2622, cell2623]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327

end


