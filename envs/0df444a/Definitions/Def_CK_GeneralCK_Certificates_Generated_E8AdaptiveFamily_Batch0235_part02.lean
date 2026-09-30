-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:48:23.420857+00:00
-- url     : https://prove2.me/theorems/7119e217-8383-4198-8432-1ccce6044171
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0235 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0235_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1885 : GaussianRat :=
  ⟨-236112247/1000000000, 65243249/500000000⟩
def contact1885 : RatBall := localContactBall tau1885 center1885
def work1885 : RoundedTauEval :=
  evalTau precision tau1885 contact1885 logTwoBall

theorem center_sq1885 : (center1885.re : ℝ)^2 +
    (center1885.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1885]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1885 : work1885.theta.ok = true ∧
    work1885.jac.invOK = true ∧ acceptsUnitSq work1885.out = true := by decide +kernel

def cell1885 : CellCertificate where
  tauBall := tau1885
  contactCenter := center1885
  contactBall := contact1885
  work := work1885
  center_sq := center_sq1885
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1885.1
  jac_ok := checks1885.2.1
  accepted := checks1885.2.2

def tau1886 : RatBall :=
  ⟨⟨-109/320, 69/320⟩, 3/640⟩
def center1886 : GaussianRat :=
  ⟨-236668663/1000000000, 134444337/1000000000⟩
def contact1886 : RatBall := localContactBall tau1886 center1886
def work1886 : RoundedTauEval :=
  evalTau precision tau1886 contact1886 logTwoBall

theorem center_sq1886 : (center1886.re : ℝ)^2 +
    (center1886.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1886]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1886 : work1886.theta.ok = true ∧
    work1886.jac.invOK = true ∧ acceptsUnitSq work1886.out = true := by decide +kernel

def cell1886 : CellCertificate where
  tauBall := tau1886
  contactCenter := center1886
  contactBall := contact1886
  work := work1886
  center_sq := center_sq1886
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1886.1
  jac_ok := checks1886.2.1
  accepted := checks1886.2.2

def tau1887 : RatBall :=
  ⟨⟨-107/320, 69/320⟩, 3/640⟩
def center1887 : GaussianRat :=
  ⟨-58174707/250000000, 67503627/500000000⟩
def contact1887 : RatBall := localContactBall tau1887 center1887
def work1887 : RoundedTauEval :=
  evalTau precision tau1887 contact1887 logTwoBall

theorem center_sq1887 : (center1887.re : ℝ)^2 +
    (center1887.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1887]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235


