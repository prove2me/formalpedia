-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:46.854234+00:00
-- url     : https://prove2.me/theorems/fafcae31-3965-492b-a051-3dbb25624d5a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0233 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0233_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1866 : work1866.theta.ok = true ∧
    work1866.jac.invOK = true ∧ acceptsUnitSq work1866.out = true := by decide +kernel

def cell1866 : CellCertificate where
  tauBall := tau1866
  contactCenter := center1866
  contactBall := contact1866
  work := work1866
  center_sq := center_sq1866
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1866.1
  jac_ok := checks1866.2.1
  accepted := checks1866.2.2

def tau1867 : RatBall :=
  ⟨⟨101/320, -15/64⟩, 3/640⟩
def center1867 : GaussianRat :=
  ⟨13899213/62500000, -2975829/20000000⟩
def contact1867 : RatBall := localContactBall tau1867 center1867
def work1867 : RoundedTauEval :=
  evalTau precision tau1867 contact1867 logTwoBall

theorem center_sq1867 : (center1867.re : ℝ)^2 +
    (center1867.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1867]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1867 : work1867.theta.ok = true ∧
    work1867.jac.invOK = true ∧ acceptsUnitSq work1867.out = true := by decide +kernel

def cell1867 : CellCertificate where
  tauBall := tau1867
  contactCenter := center1867
  contactBall := contact1867
  work := work1867
  center_sq := center_sq1867
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1867.1
  jac_ok := checks1867.2.1
  accepted := checks1867.2.2

def tau1868 : RatBall :=
  ⟨⟨103/320, -15/64⟩, 3/640⟩
def center1868 : GaussianRat :=
  ⟨14151969/62500000, -148191091/1000000000⟩
def contact1868 : RatBall := localContactBall tau1868 center1868
def work1868 : RoundedTauEval :=
  evalTau precision tau1868 contact1868 logTwoBall

theorem center_sq1868 : (center1868.re : ℝ)^2 +
    (center1868.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1868]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1868 : work1868.theta.ok = true ∧
    work1868.jac.invOK = true ∧ acceptsUnitSq work1868.out = true := by decide +kernel

def cell1868 : CellCertificate where
  tauBall := tau1868
  contactCenter := center1868
  contactBall := contact1868
  work := work1868
  center_sq := center_sq1868
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1868.1
  jac_ok := checks1868.2.1
  accepted := checks1868.2.2

def tau1869 : RatBall :=
  ⟨⟨101/320, -73/320⟩, 3/640⟩
def center1869 : GaussianRat :=
  ⟨44359939/200000000, -72370703/500000000⟩
def contact1869 : RatBall := localContactBall tau1869 center1869

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233


