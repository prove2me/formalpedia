-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0234
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0234
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:35:55.4614+00:00
-- url     : https://prove2.me/theorems/e0a2b11e-8280-4321-a6c4-0b7b55c508d0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0234.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1872 : RatBall :=
  ⟨⟨21/64, -73/320⟩, 3/640⟩
def center1872 : GaussianRat :=
  ⟨229856067/1000000000, -5742857/40000000⟩
def contact1872 : RatBall := localContactBall tau1872 center1872
def work1872 : RoundedTauEval :=
  evalTau precision tau1872 contact1872 logTwoBall

theorem center_sq1872 : (center1872.re : ℝ)^2 +
    (center1872.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1872]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1872 : work1872.theta.ok = true ∧
    work1872.jac.invOK = true ∧ acceptsUnitSq work1872.out = true := by decide +kernel

def cell1872 : CellCertificate where
  tauBall := tau1872
  contactCenter := center1872
  contactBall := contact1872
  work := work1872
  center_sq := center_sq1872
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1872.1
  jac_ok := checks1872.2.1
  accepted := checks1872.2.2

def tau1873 : RatBall :=
  ⟨⟨21/64, -71/320⟩, 3/640⟩
def center1873 : GaussianRat :=
  ⟨45854809/200000000, -139564933/1000000000⟩
def contact1873 : RatBall := localContactBall tau1873 center1873
def work1873 : RoundedTauEval :=
  evalTau precision tau1873 contact1873 logTwoBall

theorem center_sq1873 : (center1873.re : ℝ)^2 +
    (center1873.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1873]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1873 : work1873.theta.ok = true ∧
    work1873.jac.invOK = true ∧ acceptsUnitSq work1873.out = true := by decide +kernel

def cell1873 : CellCertificate where
  tauBall := tau1873
  contactCenter := center1873
  contactBall := contact1873
  work := work1873
  center_sq := center_sq1873
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1873.1
  jac_ok := checks1873.2.1
  accepted := checks1873.2.2

def tau1874 : RatBall :=
  ⟨⟨107/320, -71/320⟩, 3/640⟩
def center1874 : GaussianRat :=
  ⟨58317051/250000000, -34747303/250000000⟩
def contact1874 : RatBall := localContactBall tau1874 center1874
def work1874 : RoundedTauEval :=
  evalTau precision tau1874 contact1874 logTwoBall

theorem center_sq1874 : (center1874.re : ℝ)^2 +
    (center1874.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1874]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1874 : work1874.theta.ok = true ∧
    work1874.jac.invOK = true ∧ acceptsUnitSq work1874.out = true := by decide +kernel

def cell1874 : CellCertificate where
  tauBall := tau1874
  contactCenter := center1874
  contactBall := contact1874
  work := work1874
  center_sq := center_sq1874
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1874.1
  jac_ok := checks1874.2.1
  accepted := checks1874.2.2

def tau1875 : RatBall :=
  ⟨⟨21/64, -69/320⟩, 3/640⟩
def center1875 : GaussianRat :=
  ⟨57177633/250000000, -13556449/100000000⟩
def contact1875 : RatBall := localContactBall tau1875 center1875
def work1875 : RoundedTauEval :=
  evalTau precision tau1875 contact1875 logTwoBall

theorem center_sq1875 : (center1875.re : ℝ)^2 +
    (center1875.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1875]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1875 : work1875.theta.ok = true ∧
    work1875.jac.invOK = true ∧ acceptsUnitSq work1875.out = true := by decide +kernel

def cell1875 : CellCertificate where
  tauBall := tau1875
  contactCenter := center1875
  contactBall := contact1875
  work := work1875
  center_sq := center_sq1875
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1875.1
  jac_ok := checks1875.2.1
  accepted := checks1875.2.2

def tau1876 : RatBall :=
  ⟨⟨107/320, -69/320⟩, 3/640⟩
def center1876 : GaussianRat :=
  ⟨58174707/250000000, -67503627/500000000⟩
def contact1876 : RatBall := localContactBall tau1876 center1876
def work1876 : RoundedTauEval :=
  evalTau precision tau1876 contact1876 logTwoBall

theorem center_sq1876 : (center1876.re : ℝ)^2 +
    (center1876.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1876]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1876 : work1876.theta.ok = true ∧
    work1876.jac.invOK = true ∧ acceptsUnitSq work1876.out = true := by decide +kernel

def cell1876 : CellCertificate where
  tauBall := tau1876
  contactCenter := center1876
  contactBall := contact1876
  work := work1876
  center_sq := center_sq1876
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1876.1
  jac_ok := checks1876.2.1
  accepted := checks1876.2.2

def tau1877 : RatBall :=
  ⟨⟨109/320, -69/320⟩, 3/640⟩
def center1877 : GaussianRat :=
  ⟨236668663/1000000000, -134444337/1000000000⟩
def contact1877 : RatBall := localContactBall tau1877 center1877
def work1877 : RoundedTauEval :=
  evalTau precision tau1877 contact1877 logTwoBall

theorem center_sq1877 : (center1877.re : ℝ)^2 +
    (center1877.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1877]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1877 : work1877.theta.ok = true ∧
    work1877.jac.invOK = true ∧ acceptsUnitSq work1877.out = true := by decide +kernel

def cell1877 : CellCertificate where
  tauBall := tau1877
  contactCenter := center1877
  contactBall := contact1877
  work := work1877
  center_sq := center_sq1877
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1877.1
  jac_ok := checks1877.2.1
  accepted := checks1877.2.2

def tau1878 : RatBall :=
  ⟨⟨109/320, -67/320⟩, 3/640⟩
def center1878 : GaussianRat :=
  ⟨236112247/1000000000, -65243249/500000000⟩
def contact1878 : RatBall := localContactBall tau1878 center1878
def work1878 : RoundedTauEval :=
  evalTau precision tau1878 contact1878 logTwoBall

theorem center_sq1878 : (center1878.re : ℝ)^2 +
    (center1878.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1878]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1878 : work1878.theta.ok = true ∧
    work1878.jac.invOK = true ∧ acceptsUnitSq work1878.out = true := by decide +kernel

def cell1878 : CellCertificate where
  tauBall := tau1878
  contactCenter := center1878
  contactBall := contact1878
  work := work1878
  center_sq := center_sq1878
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1878.1
  jac_ok := checks1878.2.1
  accepted := checks1878.2.2

def tau1879 : RatBall :=
  ⟨⟨109/320, -13/64⟩, 3/640⟩
def center1879 : GaussianRat :=
  ⟨29446781/125000000, -63266993/500000000⟩
def contact1879 : RatBall := localContactBall tau1879 center1879
def work1879 : RoundedTauEval :=
  evalTau precision tau1879 contact1879 logTwoBall

theorem center_sq1879 : (center1879.re : ℝ)^2 +
    (center1879.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1879]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1879 : work1879.theta.ok = true ∧
    work1879.jac.invOK = true ∧ acceptsUnitSq work1879.out = true := by decide +kernel

def cell1879 : CellCertificate where
  tauBall := tau1879
  contactCenter := center1879
  contactBall := contact1879
  work := work1879
  center_sq := center_sq1879
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1879.1
  jac_ok := checks1879.2.1
  accepted := checks1879.2.2

def cells : List CellCertificate := [cell1872, cell1873, cell1874, cell1875, cell1876, cell1877, cell1878, cell1879]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234

end


