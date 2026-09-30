-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0237
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0237
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:40:41.465721+00:00
-- url     : https://prove2.me/theorems/0af66638-bb58-4aed-9885-b4b29ba7e3c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0237.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1896 : RatBall :=
  ⟨⟨-101/320, 15/64⟩, 3/640⟩
def center1896 : GaussianRat :=
  ⟨-13899213/62500000, 2975829/20000000⟩
def contact1896 : RatBall := localContactBall tau1896 center1896
def work1896 : RoundedTauEval :=
  evalTau precision tau1896 contact1896 logTwoBall

theorem center_sq1896 : (center1896.re : ℝ)^2 +
    (center1896.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1896]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1896 : work1896.theta.ok = true ∧
    work1896.jac.invOK = true ∧ acceptsUnitSq work1896.out = true := by decide +kernel

def cell1896 : CellCertificate where
  tauBall := tau1896
  contactCenter := center1896
  contactBall := contact1896
  work := work1896
  center_sq := center_sq1896
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1896.1
  jac_ok := checks1896.2.1
  accepted := checks1896.2.2

def tau1897 : RatBall :=
  ⟨⟨-103/320, 77/320⟩, 3/640⟩
def center1897 : GaussianRat :=
  ⟨-113522317/500000000, 152229153/1000000000⟩
def contact1897 : RatBall := localContactBall tau1897 center1897
def work1897 : RoundedTauEval :=
  evalTau precision tau1897 contact1897 logTwoBall

theorem center_sq1897 : (center1897.re : ℝ)^2 +
    (center1897.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1897]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1897 : work1897.theta.ok = true ∧
    work1897.jac.invOK = true ∧ acceptsUnitSq work1897.out = true := by decide +kernel

def cell1897 : CellCertificate where
  tauBall := tau1897
  contactCenter := center1897
  contactBall := contact1897
  work := work1897
  center_sq := center_sq1897
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1897.1
  jac_ok := checks1897.2.1
  accepted := checks1897.2.2

def tau1898 : RatBall :=
  ⟨⟨-101/320, 77/320⟩, 3/640⟩
def center1898 : GaussianRat :=
  ⟨-111496867/500000000, 152848327/1000000000⟩
def contact1898 : RatBall := localContactBall tau1898 center1898
def work1898 : RoundedTauEval :=
  evalTau precision tau1898 contact1898 logTwoBall

theorem center_sq1898 : (center1898.re : ℝ)^2 +
    (center1898.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1898]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1898 : work1898.theta.ok = true ∧
    work1898.jac.invOK = true ∧ acceptsUnitSq work1898.out = true := by decide +kernel

def cell1898 : CellCertificate where
  tauBall := tau1898
  contactCenter := center1898
  contactBall := contact1898
  work := work1898
  center_sq := center_sq1898
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1898.1
  jac_ok := checks1898.2.1
  accepted := checks1898.2.2

def tau1899 : RatBall :=
  ⟨⟨-101/320, 79/320⟩, 3/640⟩
def center1899 : GaussianRat :=
  ⟨-111809453/500000000, 156912213/1000000000⟩
def contact1899 : RatBall := localContactBall tau1899 center1899
def work1899 : RoundedTauEval :=
  evalTau precision tau1899 contact1899 logTwoBall

theorem center_sq1899 : (center1899.re : ℝ)^2 +
    (center1899.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1899]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1899 : work1899.theta.ok = true ∧
    work1899.jac.invOK = true ∧ acceptsUnitSq work1899.out = true := by decide +kernel

def cell1899 : CellCertificate where
  tauBall := tau1899
  contactCenter := center1899
  contactBall := contact1899
  work := work1899
  center_sq := center_sq1899
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1899.1
  jac_ok := checks1899.2.1
  accepted := checks1899.2.2

def tau1900 : RatBall :=
  ⟨⟨-99/320, 77/320⟩, 3/640⟩
def center1900 : GaussianRat :=
  ⟨-218923989/1000000000, 38365123/250000000⟩
def contact1900 : RatBall := localContactBall tau1900 center1900
def work1900 : RoundedTauEval :=
  evalTau precision tau1900 contact1900 logTwoBall

theorem center_sq1900 : (center1900.re : ℝ)^2 +
    (center1900.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1900]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1900 : work1900.theta.ok = true ∧
    work1900.jac.invOK = true ∧ acceptsUnitSq work1900.out = true := by decide +kernel

def cell1900 : CellCertificate where
  tauBall := tau1900
  contactCenter := center1900
  contactBall := contact1900
  work := work1900
  center_sq := center_sq1900
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1900.1
  jac_ok := checks1900.2.1
  accepted := checks1900.2.2

def tau1901 : RatBall :=
  ⟨⟨-97/320, 77/320⟩, 3/640⟩
def center1901 : GaussianRat :=
  ⟨-10741779/50000000, 300909/1953125⟩
def contact1901 : RatBall := localContactBall tau1901 center1901
def work1901 : RoundedTauEval :=
  evalTau precision tau1901 contact1901 logTwoBall

theorem center_sq1901 : (center1901.re : ℝ)^2 +
    (center1901.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1901]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1901 : work1901.theta.ok = true ∧
    work1901.jac.invOK = true ∧ acceptsUnitSq work1901.out = true := by decide +kernel

def cell1901 : CellCertificate where
  tauBall := tau1901
  contactCenter := center1901
  contactBall := contact1901
  work := work1901
  center_sq := center_sq1901
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1901.1
  jac_ok := checks1901.2.1
  accepted := checks1901.2.2

def tau1902 : RatBall :=
  ⟨⟨-99/320, 79/320⟩, 3/640⟩
def center1902 : GaussianRat :=
  ⟨-109770971/500000000, 78771627/500000000⟩
def contact1902 : RatBall := localContactBall tau1902 center1902
def work1902 : RoundedTauEval :=
  evalTau precision tau1902 contact1902 logTwoBall

theorem center_sq1902 : (center1902.re : ℝ)^2 +
    (center1902.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1902]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1902 : work1902.theta.ok = true ∧
    work1902.jac.invOK = true ∧ acceptsUnitSq work1902.out = true := by decide +kernel

def cell1902 : CellCertificate where
  tauBall := tau1902
  contactCenter := center1902
  contactBall := contact1902
  work := work1902
  center_sq := center_sq1902
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1902.1
  jac_ok := checks1902.2.1
  accepted := checks1902.2.2

def tau1903 : RatBall :=
  ⟨⟨-97/320, 79/320⟩, 3/640⟩
def center1903 : GaussianRat :=
  ⟨-215446071/1000000000, 158166863/1000000000⟩
def contact1903 : RatBall := localContactBall tau1903 center1903
def work1903 : RoundedTauEval :=
  evalTau precision tau1903 contact1903 logTwoBall

theorem center_sq1903 : (center1903.re : ℝ)^2 +
    (center1903.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1903]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1903 : work1903.theta.ok = true ∧
    work1903.jac.invOK = true ∧ acceptsUnitSq work1903.out = true := by decide +kernel

def cell1903 : CellCertificate where
  tauBall := tau1903
  contactCenter := center1903
  contactBall := contact1903
  work := work1903
  center_sq := center_sq1903
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1903.1
  jac_ok := checks1903.2.1
  accepted := checks1903.2.2

def cells : List CellCertificate := [cell1896, cell1897, cell1898, cell1899, cell1900, cell1901, cell1902, cell1903]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237

end


