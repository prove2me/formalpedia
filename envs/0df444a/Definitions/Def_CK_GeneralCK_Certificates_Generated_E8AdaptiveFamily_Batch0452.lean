-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0452
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0452
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:49:25.639017+00:00
-- url     : https://prove2.me/theorems/42f5d928-b5d2-4d0d-9438-08223f2f0a1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0452.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3616 : RatBall :=
  ⟨⟨9/128, 49/128⟩, 3/1280⟩
def center3616 : GaussianRat :=
  ⟨57276093/1000000000, 139153977/500000000⟩
def contact3616 : RatBall := localContactBall tau3616 center3616
def work3616 : RoundedTauEval :=
  evalTau precision tau3616 contact3616 logTwoBall

theorem center_sq3616 : (center3616.re : ℝ)^2 +
    (center3616.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3616]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3616 : work3616.theta.ok = true ∧
    work3616.jac.invOK = true ∧ acceptsUnitSq work3616.out = true := by decide +kernel

def cell3616 : CellCertificate where
  tauBall := tau3616
  contactCenter := center3616
  contactBall := contact3616
  work := work3616
  center_sq := center_sq3616
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3616.1
  jac_ok := checks3616.2.1
  accepted := checks3616.2.2

def tau3617 : RatBall :=
  ⟨⟨47/640, 49/128⟩, 3/1280⟩
def center3617 : GaussianRat :=
  ⟨2392131/40000000, 55627861/200000000⟩
def contact3617 : RatBall := localContactBall tau3617 center3617
def work3617 : RoundedTauEval :=
  evalTau precision tau3617 contact3617 logTwoBall

theorem center_sq3617 : (center3617.re : ℝ)^2 +
    (center3617.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3617]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3617 : work3617.theta.ok = true ∧
    work3617.jac.invOK = true ∧ acceptsUnitSq work3617.out = true := by decide +kernel

def cell3617 : CellCertificate where
  tauBall := tau3617
  contactCenter := center3617
  contactBall := contact3617
  work := work3617
  center_sq := center_sq3617
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3617.1
  jac_ok := checks3617.2.1
  accepted := checks3617.2.2

def tau3618 : RatBall :=
  ⟨⟨9/128, 247/640⟩, 3/1280⟩
def center3618 : GaussianRat :=
  ⟨2872117/50000000, 14041993/50000000⟩
def contact3618 : RatBall := localContactBall tau3618 center3618
def work3618 : RoundedTauEval :=
  evalTau precision tau3618 contact3618 logTwoBall

theorem center_sq3618 : (center3618.re : ℝ)^2 +
    (center3618.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3618]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3618 : work3618.theta.ok = true ∧
    work3618.jac.invOK = true ∧ acceptsUnitSq work3618.out = true := by decide +kernel

def cell3618 : CellCertificate where
  tauBall := tau3618
  contactCenter := center3618
  contactBall := contact3618
  work := work3618
  center_sq := center_sq3618
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3618.1
  jac_ok := checks3618.2.1
  accepted := checks3618.2.2

def tau3619 : RatBall :=
  ⟨⟨47/640, 247/640⟩, 3/1280⟩
def center3619 : GaussianRat :=
  ⟨59976659/1000000000, 70167217/250000000⟩
def contact3619 : RatBall := localContactBall tau3619 center3619
def work3619 : RoundedTauEval :=
  evalTau precision tau3619 contact3619 logTwoBall

theorem center_sq3619 : (center3619.re : ℝ)^2 +
    (center3619.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3619]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3619 : work3619.theta.ok = true ∧
    work3619.jac.invOK = true ∧ acceptsUnitSq work3619.out = true := by decide +kernel

def cell3619 : CellCertificate where
  tauBall := tau3619
  contactCenter := center3619
  contactBall := contact3619
  work := work3619
  center_sq := center_sq3619
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3619.1
  jac_ok := checks3619.2.1
  accepted := checks3619.2.2

def tau3620 : RatBall :=
  ⟨⟨33/640, 249/640⟩, 3/1280⟩
def center3620 : GaussianRat :=
  ⟨42315903/1000000000, 284264849/1000000000⟩
def contact3620 : RatBall := localContactBall tau3620 center3620
def work3620 : RoundedTauEval :=
  evalTau precision tau3620 contact3620 logTwoBall

theorem center_sq3620 : (center3620.re : ℝ)^2 +
    (center3620.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3620]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3620 : work3620.theta.ok = true ∧
    work3620.jac.invOK = true ∧ acceptsUnitSq work3620.out = true := by decide +kernel

def cell3620 : CellCertificate where
  tauBall := tau3620
  contactCenter := center3620
  contactBall := contact3620
  work := work3620
  center_sq := center_sq3620
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3620.1
  jac_ok := checks3620.2.1
  accepted := checks3620.2.2

def tau3621 : RatBall :=
  ⟨⟨7/128, 249/640⟩, 3/1280⟩
def center3621 : GaussianRat :=
  ⟨22435003/500000000, 284135717/1000000000⟩
def contact3621 : RatBall := localContactBall tau3621 center3621
def work3621 : RoundedTauEval :=
  evalTau precision tau3621 contact3621 logTwoBall

theorem center_sq3621 : (center3621.re : ℝ)^2 +
    (center3621.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3621]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3621 : work3621.theta.ok = true ∧
    work3621.jac.invOK = true ∧ acceptsUnitSq work3621.out = true := by decide +kernel

def cell3621 : CellCertificate where
  tauBall := tau3621
  contactCenter := center3621
  contactBall := contact3621
  work := work3621
  center_sq := center_sq3621
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3621.1
  jac_ok := checks3621.2.1
  accepted := checks3621.2.2

def tau3622 : RatBall :=
  ⟨⟨33/640, 251/640⟩, 3/1280⟩
def center3622 : GaussianRat :=
  ⟨42442179/1000000000, 286823589/1000000000⟩
def contact3622 : RatBall := localContactBall tau3622 center3622
def work3622 : RoundedTauEval :=
  evalTau precision tau3622 contact3622 logTwoBall

theorem center_sq3622 : (center3622.re : ℝ)^2 +
    (center3622.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3622]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3622 : work3622.theta.ok = true ∧
    work3622.jac.invOK = true ∧ acceptsUnitSq work3622.out = true := by decide +kernel

def cell3622 : CellCertificate where
  tauBall := tau3622
  contactCenter := center3622
  contactBall := contact3622
  work := work3622
  center_sq := center_sq3622
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3622.1
  jac_ok := checks3622.2.1
  accepted := checks3622.2.2

def tau3623 : RatBall :=
  ⟨⟨7/128, 251/640⟩, 3/1280⟩
def center3623 : GaussianRat :=
  ⟨45003787/1000000000, 57338531/200000000⟩
def contact3623 : RatBall := localContactBall tau3623 center3623
def work3623 : RoundedTauEval :=
  evalTau precision tau3623 contact3623 logTwoBall

theorem center_sq3623 : (center3623.re : ℝ)^2 +
    (center3623.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3623]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3623 : work3623.theta.ok = true ∧
    work3623.jac.invOK = true ∧ acceptsUnitSq work3623.out = true := by decide +kernel

def cell3623 : CellCertificate where
  tauBall := tau3623
  contactCenter := center3623
  contactBall := contact3623
  work := work3623
  center_sq := center_sq3623
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3623.1
  jac_ok := checks3623.2.1
  accepted := checks3623.2.2

def cells : List CellCertificate := [cell3616, cell3617, cell3618, cell3619, cell3620, cell3621, cell3622, cell3623]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452

end


