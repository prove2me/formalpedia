-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0124_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0124_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:14:21.813673+00:00
-- url     : https://prove2.me/theorems/d53f3cf5-9079-4629-9c60-5c7358aae8ad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0124 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0992 : RatBall :=
  ⟨⟨61/160, 11/160⟩, 3/320⟩
def center0992 : GaussianRat :=
  ⟨25301093/100000000, 41411583/1000000000⟩
def contact0992 : RatBall := localContactBall tau0992 center0992
def work0992 : RoundedTauEval :=
  evalTau precision tau0992 contact0992 logTwoBall

theorem center_sq0992 : (center0992.re : ℝ)^2 +
    (center0992.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0992]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0992 : work0992.theta.ok = true ∧
    work0992.jac.invOK = true ∧ acceptsUnitSq work0992.out = true := by decide +kernel

def cell0992 : CellCertificate where
  tauBall := tau0992
  contactCenter := center0992
  contactBall := contact0992
  work := work0992
  center_sq := center_sq0992
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0992.1
  jac_ok := checks0992.2.1
  accepted := checks0992.2.2

def tau0993 : RatBall :=
  ⟨⟨63/160, 11/160⟩, 3/320⟩
def center0993 : GaussianRat :=
  ⟨260517353/1000000000, 1026213/25000000⟩
def contact0993 : RatBall := localContactBall tau0993 center0993
def work0993 : RoundedTauEval :=
  evalTau precision tau0993 contact0993 logTwoBall

theorem center_sq0993 : (center0993.re : ℝ)^2 +
    (center0993.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0993]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0993 : work0993.theta.ok = true ∧
    work0993.jac.invOK = true ∧ acceptsUnitSq work0993.out = true := by decide +kernel

def cell0993 : CellCertificate where
  tauBall := tau0993
  contactCenter := center0993
  contactBall := contact0993
  work := work0993
  center_sq := center_sq0993
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0993.1
  jac_ok := checks0993.2.1
  accepted := checks0993.2.2

def tau0994 : RatBall :=
  ⟨⟨57/160, 13/160⟩, 3/320⟩
def center0994 : GaussianRat :=
  ⟨238180443/1000000000, 24897027/500000000⟩
def contact0994 : RatBall := localContactBall tau0994 center0994
def work0994 : RoundedTauEval :=
  evalTau precision tau0994 contact0994 logTwoBall

theorem center_sq0994 : (center0994.re : ℝ)^2 +
    (center0994.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0994]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0994 : work0994.theta.ok = true ∧
    work0994.jac.invOK = true ∧ acceptsUnitSq work0994.out = true := by decide +kernel

def cell0994 : CellCertificate where
  tauBall := tau0994
  contactCenter := center0994
  contactBall := contact0994
  work := work0994
  center_sq := center_sq0994
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0994.1
  jac_ok := checks0994.2.1
  accepted := checks0994.2.2

def tau0995 : RatBall :=
  ⟨⟨59/160, 13/160⟩, 3/320⟩
def center0995 : GaussianRat :=
  ⟨245825343/1000000000, 12344447/250000000⟩
def contact0995 : RatBall := localContactBall tau0995 center0995
def work0995 : RoundedTauEval :=
  evalTau precision tau0995 contact0995 logTwoBall

theorem center_sq0995 : (center0995.re : ℝ)^2 +
    (center0995.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0995]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0995 : work0995.theta.ok = true ∧
    work0995.jac.invOK = true ∧ acceptsUnitSq work0995.out = true := by decide +kernel

def cell0995 : CellCertificate where
  tauBall := tau0995
  contactCenter := center0995
  contactBall := contact0995
  work := work0995
  center_sq := center_sq0995
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0995.1
  jac_ok := checks0995.2.1
  accepted := checks0995.2.2

def tau0996 : RatBall :=
  ⟨⟨57/160, 3/32⟩, 3/320⟩
def center0996 : GaussianRat :=
  ⟨11931267/50000000, 14368881/250000000⟩
def contact0996 : RatBall := localContactBall tau0996 center0996
def work0996 : RoundedTauEval :=
  evalTau precision tau0996 contact0996 logTwoBall

theorem center_sq0996 : (center0996.re : ℝ)^2 +
    (center0996.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0996]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0996 : work0996.theta.ok = true ∧
    work0996.jac.invOK = true ∧ acceptsUnitSq work0996.out = true := by decide +kernel

def cell0996 : CellCertificate where
  tauBall := tau0996
  contactCenter := center0996
  contactBall := contact0996
  work := work0996
  center_sq := center_sq0996
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0996.1
  jac_ok := checks0996.2.1
  accepted := checks0996.2.2

def tau0997 : RatBall :=
  ⟨⟨59/160, 3/32⟩, 3/320⟩
def center0997 : GaussianRat :=
  ⟨246278271/1000000000, 56993771/1000000000⟩
def contact0997 : RatBall := localContactBall tau0997 center0997
def work0997 : RoundedTauEval :=
  evalTau precision tau0997 contact0997 logTwoBall

theorem center_sq0997 : (center0997.re : ℝ)^2 +
    (center0997.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0997]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0997 : work0997.theta.ok = true ∧
    work0997.jac.invOK = true ∧ acceptsUnitSq work0997.out = true := by decide +kernel

def cell0997 : CellCertificate where
  tauBall := tau0997
  contactCenter := center0997
  contactBall := contact0997
  work := work0997
  center_sq := center_sq0997
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0997.1
  jac_ok := checks0997.2.1
  accepted := checks0997.2.2

def tau0998 : RatBall :=
  ⟨⟨61/160, 13/160⟩, 3/320⟩
def center0998 : GaussianRat :=
  ⟨126702243/500000000, 6119291/125000000⟩
def contact0998 : RatBall := localContactBall tau0998 center0998
def work0998 : RoundedTauEval :=
  evalTau precision tau0998 contact0998 logTwoBall

theorem center_sq0998 : (center0998.re : ℝ)^2 +
    (center0998.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0998]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124


