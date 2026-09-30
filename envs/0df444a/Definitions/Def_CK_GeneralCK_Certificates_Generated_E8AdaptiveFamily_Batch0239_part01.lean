-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:13.655048+00:00
-- url     : https://prove2.me/theorems/6a20ed3e-85c4-4186-92d1-1c80d6fb7239
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0239 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0239_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1914 : work1914.theta.ok = true ∧
    work1914.jac.invOK = true ∧ acceptsUnitSq work1914.out = true := by decide +kernel

def cell1914 : CellCertificate where
  tauBall := tau1914
  contactCenter := center1914
  contactBall := contact1914
  work := work1914
  center_sq := center_sq1914
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1914.1
  jac_ok := checks1914.2.1
  accepted := checks1914.2.2

def tau1915 : RatBall :=
  ⟨⟨-19/64, 83/320⟩, 3/640⟩
def center1915 : GaussianRat :=
  ⟨-212592873/1000000000, 33409337/200000000⟩
def contact1915 : RatBall := localContactBall tau1915 center1915
def work1915 : RoundedTauEval :=
  evalTau precision tau1915 contact1915 logTwoBall

theorem center_sq1915 : (center1915.re : ℝ)^2 +
    (center1915.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1915]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1915 : work1915.theta.ok = true ∧
    work1915.jac.invOK = true ∧ acceptsUnitSq work1915.out = true := by decide +kernel

def cell1915 : CellCertificate where
  tauBall := tau1915
  contactCenter := center1915
  contactBall := contact1915
  work := work1915
  center_sq := center_sq1915
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1915.1
  jac_ok := checks1915.2.1
  accepted := checks1915.2.2

def tau1916 : RatBall :=
  ⟨⟨-93/320, 83/320⟩, 3/640⟩
def center1916 : GaussianRat :=
  ⟨-52110811/250000000, 167692033/1000000000⟩
def contact1916 : RatBall := localContactBall tau1916 center1916
def work1916 : RoundedTauEval :=
  evalTau precision tau1916 contact1916 logTwoBall

theorem center_sq1916 : (center1916.re : ℝ)^2 +
    (center1916.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1916]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1916 : work1916.theta.ok = true ∧
    work1916.jac.invOK = true ∧ acceptsUnitSq work1916.out = true := by decide +kernel

def cell1916 : CellCertificate where
  tauBall := tau1916
  contactCenter := center1916
  contactBall := contact1916
  work := work1916
  center_sq := center_sq1916
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1916.1
  jac_ok := checks1916.2.1
  accepted := checks1916.2.2

def tau1917 : RatBall :=
  ⟨⟨-91/320, 81/320⟩, 3/640⟩
def center1917 : GaussianRat :=
  ⟨-101825843/500000000, 82077687/500000000⟩
def contact1917 : RatBall := localContactBall tau1917 center1917

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239


