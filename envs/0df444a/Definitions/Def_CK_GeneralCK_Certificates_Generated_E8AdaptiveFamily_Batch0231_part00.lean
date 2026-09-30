-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0231_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0231_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:30:51.252394+00:00
-- url     : https://prove2.me/theorems/a3b2e470-d792-43d1-8574-7ec7fd53bcd8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0231 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1848 : RatBall :=
  ⟨⟨19/64, -83/320⟩, 3/640⟩
def center1848 : GaussianRat :=
  ⟨212592873/1000000000, -33409337/200000000⟩
def contact1848 : RatBall := localContactBall tau1848 center1848
def work1848 : RoundedTauEval :=
  evalTau precision tau1848 contact1848 logTwoBall

theorem center_sq1848 : (center1848.re : ℝ)^2 +
    (center1848.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1848]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1848 : work1848.theta.ok = true ∧
    work1848.jac.invOK = true ∧ acceptsUnitSq work1848.out = true := by decide +kernel

def cell1848 : CellCertificate where
  tauBall := tau1848
  contactCenter := center1848
  contactBall := contact1848
  work := work1848
  center_sq := center_sq1848
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1848.1
  jac_ok := checks1848.2.1
  accepted := checks1848.2.2

def tau1849 : RatBall :=
  ⟨⟨93/320, -81/320⟩, 3/640⟩
def center1849 : GaussianRat :=
  ⟨103905761/500000000, -163537217/1000000000⟩
def contact1849 : RatBall := localContactBall tau1849 center1849
def work1849 : RoundedTauEval :=
  evalTau precision tau1849 contact1849 logTwoBall

theorem center_sq1849 : (center1849.re : ℝ)^2 +
    (center1849.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1849]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1849 : work1849.theta.ok = true ∧
    work1849.jac.invOK = true ∧ acceptsUnitSq work1849.out = true := by decide +kernel

def cell1849 : CellCertificate where
  tauBall := tau1849
  contactCenter := center1849
  contactBall := contact1849
  work := work1849
  center_sq := center_sq1849
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1849.1
  jac_ok := checks1849.2.1
  accepted := checks1849.2.2

def tau1850 : RatBall :=
  ⟨⟨19/64, -81/320⟩, 3/640⟩
def center1850 : GaussianRat :=
  ⟨211952789/1000000000, -162910673/1000000000⟩
def contact1850 : RatBall := localContactBall tau1850 center1850
def work1850 : RoundedTauEval :=
  evalTau precision tau1850 contact1850 logTwoBall

theorem center_sq1850 : (center1850.re : ℝ)^2 +
    (center1850.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1850]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1850 : work1850.theta.ok = true ∧
    work1850.jac.invOK = true ∧ acceptsUnitSq work1850.out = true := by decide +kernel

def cell1850 : CellCertificate where
  tauBall := tau1850
  contactCenter := center1850
  contactBall := contact1850
  work := work1850
  center_sq := center_sq1850
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1850.1
  jac_ok := checks1850.2.1
  accepted := checks1850.2.2

def tau1851 : RatBall :=
  ⟨⟨93/320, -79/320⟩, 3/640⟩
def center1851 : GaussianRat :=
  ⟨207198371/1000000000, -15939079/100000000⟩
def contact1851 : RatBall := localContactBall tau1851 center1851
def work1851 : RoundedTauEval :=
  evalTau precision tau1851 contact1851 logTwoBall

theorem center_sq1851 : (center1851.re : ℝ)^2 +
    (center1851.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1851]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1851 : work1851.theta.ok = true ∧
    work1851.jac.invOK = true ∧ acceptsUnitSq work1851.out = true := by decide +kernel

def cell1851 : CellCertificate where
  tauBall := tau1851
  contactCenter := center1851
  contactBall := contact1851
  work := work1851
  center_sq := center_sq1851
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1851.1
  jac_ok := checks1851.2.1
  accepted := checks1851.2.2

def tau1852 : RatBall :=
  ⟨⟨19/64, -79/320⟩, 3/640⟩
def center1852 : GaussianRat :=
  ⟨211331481/1000000000, -158782791/1000000000⟩
def contact1852 : RatBall := localContactBall tau1852 center1852

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231


