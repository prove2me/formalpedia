-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0232
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0232
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:26:54.644509+00:00
-- url     : https://prove2.me/theorems/933e839c-514d-467f-a43f-ef14ac87df31
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0232.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1856 : RatBall :=
  ⟨⟨97/320, -83/320⟩, 3/640⟩
def center1856 : GaussianRat :=
  ⟨108361733/500000000, -83196503/500000000⟩
def contact1856 : RatBall := localContactBall tau1856 center1856
def work1856 : RoundedTauEval :=
  evalTau precision tau1856 contact1856 logTwoBall

theorem center_sq1856 : (center1856.re : ℝ)^2 +
    (center1856.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1856]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1856 : work1856.theta.ok = true ∧
    work1856.jac.invOK = true ∧ acceptsUnitSq work1856.out = true := by decide +kernel

def cell1856 : CellCertificate where
  tauBall := tau1856
  contactCenter := center1856
  contactBall := contact1856
  work := work1856
  center_sq := center_sq1856
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1856.1
  jac_ok := checks1856.2.1
  accepted := checks1856.2.2

def tau1857 : RatBall :=
  ⟨⟨99/320, -83/320⟩, 3/640⟩
def center1857 : GaussianRat :=
  ⟨110417413/500000000, -165731261/1000000000⟩
def contact1857 : RatBall := localContactBall tau1857 center1857
def work1857 : RoundedTauEval :=
  evalTau precision tau1857 contact1857 logTwoBall

theorem center_sq1857 : (center1857.re : ℝ)^2 +
    (center1857.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1857]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1857 : work1857.theta.ok = true ∧
    work1857.jac.invOK = true ∧ acceptsUnitSq work1857.out = true := by decide +kernel

def cell1857 : CellCertificate where
  tauBall := tau1857
  contactCenter := center1857
  contactBall := contact1857
  work := work1857
  center_sq := center_sq1857
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1857.1
  jac_ok := checks1857.2.1
  accepted := checks1857.2.2

def tau1858 : RatBall :=
  ⟨⟨97/320, -81/320⟩, 3/640⟩
def center1858 : GaussianRat :=
  ⟨108037641/500000000, -81137999/500000000⟩
def contact1858 : RatBall := localContactBall tau1858 center1858
def work1858 : RoundedTauEval :=
  evalTau precision tau1858 contact1858 logTwoBall

theorem center_sq1858 : (center1858.re : ℝ)^2 +
    (center1858.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1858]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1858 : work1858.theta.ok = true ∧
    work1858.jac.invOK = true ∧ acceptsUnitSq work1858.out = true := by decide +kernel

def cell1858 : CellCertificate where
  tauBall := tau1858
  contactCenter := center1858
  contactBall := contact1858
  work := work1858
  center_sq := center_sq1858
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1858.1
  jac_ok := checks1858.2.1
  accepted := checks1858.2.2

def tau1859 : RatBall :=
  ⟨⟨99/320, -81/320⟩, 3/640⟩
def center1859 : GaussianRat :=
  ⟨55044701/250000000, -161633449/1000000000⟩
def contact1859 : RatBall := localContactBall tau1859 center1859
def work1859 : RoundedTauEval :=
  evalTau precision tau1859 contact1859 logTwoBall

theorem center_sq1859 : (center1859.re : ℝ)^2 +
    (center1859.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1859]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1859 : work1859.theta.ok = true ∧
    work1859.jac.invOK = true ∧ acceptsUnitSq work1859.out = true := by decide +kernel

def cell1859 : CellCertificate where
  tauBall := tau1859
  contactCenter := center1859
  contactBall := contact1859
  work := work1859
  center_sq := center_sq1859
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1859.1
  jac_ok := checks1859.2.1
  accepted := checks1859.2.2

def tau1860 : RatBall :=
  ⟨⟨97/320, -79/320⟩, 3/640⟩
def center1860 : GaussianRat :=
  ⟨215446071/1000000000, -158166863/1000000000⟩
def contact1860 : RatBall := localContactBall tau1860 center1860
def work1860 : RoundedTauEval :=
  evalTau precision tau1860 contact1860 logTwoBall

theorem center_sq1860 : (center1860.re : ℝ)^2 +
    (center1860.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1860]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1860 : work1860.theta.ok = true ∧
    work1860.jac.invOK = true ∧ acceptsUnitSq work1860.out = true := by decide +kernel

def cell1860 : CellCertificate where
  tauBall := tau1860
  contactCenter := center1860
  contactBall := contact1860
  work := work1860
  center_sq := center_sq1860
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1860.1
  jac_ok := checks1860.2.1
  accepted := checks1860.2.2

def tau1861 : RatBall :=
  ⟨⟨99/320, -79/320⟩, 3/640⟩
def center1861 : GaussianRat :=
  ⟨109770971/500000000, -78771627/500000000⟩
def contact1861 : RatBall := localContactBall tau1861 center1861
def work1861 : RoundedTauEval :=
  evalTau precision tau1861 contact1861 logTwoBall

theorem center_sq1861 : (center1861.re : ℝ)^2 +
    (center1861.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1861]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1861 : work1861.theta.ok = true ∧
    work1861.jac.invOK = true ∧ acceptsUnitSq work1861.out = true := by decide +kernel

def cell1861 : CellCertificate where
  tauBall := tau1861
  contactCenter := center1861
  contactBall := contact1861
  work := work1861
  center_sq := center_sq1861
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1861.1
  jac_ok := checks1861.2.1
  accepted := checks1861.2.2

def tau1862 : RatBall :=
  ⟨⟨97/320, -77/320⟩, 3/640⟩
def center1862 : GaussianRat :=
  ⟨10741779/50000000, -300909/1953125⟩
def contact1862 : RatBall := localContactBall tau1862 center1862
def work1862 : RoundedTauEval :=
  evalTau precision tau1862 contact1862 logTwoBall

theorem center_sq1862 : (center1862.re : ℝ)^2 +
    (center1862.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1862]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1862 : work1862.theta.ok = true ∧
    work1862.jac.invOK = true ∧ acceptsUnitSq work1862.out = true := by decide +kernel

def cell1862 : CellCertificate where
  tauBall := tau1862
  contactCenter := center1862
  contactBall := contact1862
  work := work1862
  center_sq := center_sq1862
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1862.1
  jac_ok := checks1862.2.1
  accepted := checks1862.2.2

def tau1863 : RatBall :=
  ⟨⟨99/320, -77/320⟩, 3/640⟩
def center1863 : GaussianRat :=
  ⟨218923989/1000000000, -38365123/250000000⟩
def contact1863 : RatBall := localContactBall tau1863 center1863
def work1863 : RoundedTauEval :=
  evalTau precision tau1863 contact1863 logTwoBall

theorem center_sq1863 : (center1863.re : ℝ)^2 +
    (center1863.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1863]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1863 : work1863.theta.ok = true ∧
    work1863.jac.invOK = true ∧ acceptsUnitSq work1863.out = true := by decide +kernel

def cell1863 : CellCertificate where
  tauBall := tau1863
  contactCenter := center1863
  contactBall := contact1863
  work := work1863
  center_sq := center_sq1863
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1863.1
  jac_ok := checks1863.2.1
  accepted := checks1863.2.2

def cells : List CellCertificate := [cell1856, cell1857, cell1858, cell1859, cell1860, cell1861, cell1862, cell1863]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232

end


