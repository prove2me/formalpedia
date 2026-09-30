-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0111
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0111
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:13:11.154463+00:00
-- url     : https://prove2.me/theorems/a2f263a9-df71-488d-80da-1162225e7762
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0111.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0888 : RatBall :=
  ⟨⟨-39/160, 41/160⟩, 3/320⟩
def center0888 : GaussianRat :=
  ⟨-44113519/250000000, 170094077/1000000000⟩
def contact0888 : RatBall := localContactBall tau0888 center0888
def work0888 : RoundedTauEval :=
  evalTau precision tau0888 contact0888 logTwoBall

theorem center_sq0888 : (center0888.re : ℝ)^2 +
    (center0888.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0888]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0888 : work0888.theta.ok = true ∧
    work0888.jac.invOK = true ∧ acceptsUnitSq work0888.out = true := by decide +kernel

def cell0888 : CellCertificate where
  tauBall := tau0888
  contactCenter := center0888
  contactBall := contact0888
  work := work0888
  center_sq := center_sq0888
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0888.1
  jac_ok := checks0888.2.1
  accepted := checks0888.2.2

def tau0889 : RatBall :=
  ⟨⟨-37/160, 41/160⟩, 3/320⟩
def center0889 : GaussianRat :=
  ⟨-167843761/1000000000, 171194117/1000000000⟩
def contact0889 : RatBall := localContactBall tau0889 center0889
def work0889 : RoundedTauEval :=
  evalTau precision tau0889 contact0889 logTwoBall

theorem center_sq0889 : (center0889.re : ℝ)^2 +
    (center0889.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0889]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0889 : work0889.theta.ok = true ∧
    work0889.jac.invOK = true ∧ acceptsUnitSq work0889.out = true := by decide +kernel

def cell0889 : CellCertificate where
  tauBall := tau0889
  contactCenter := center0889
  contactBall := contact0889
  work := work0889
  center_sq := center_sq0889
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0889.1
  jac_ok := checks0889.2.1
  accepted := checks0889.2.2

def tau0890 : RatBall :=
  ⟨⟨-39/160, 43/160⟩, 3/320⟩
def center0890 : GaussianRat :=
  ⟨-177609433/1000000000, 178692329/1000000000⟩
def contact0890 : RatBall := localContactBall tau0890 center0890
def work0890 : RoundedTauEval :=
  evalTau precision tau0890 contact0890 logTwoBall

theorem center_sq0890 : (center0890.re : ℝ)^2 +
    (center0890.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0890]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0890 : work0890.theta.ok = true ∧
    work0890.jac.invOK = true ∧ acceptsUnitSq work0890.out = true := by decide +kernel

def cell0890 : CellCertificate where
  tauBall := tau0890
  contactCenter := center0890
  contactBall := contact0890
  work := work0890
  center_sq := center_sq0890
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0890.1
  jac_ok := checks0890.2.1
  accepted := checks0890.2.2

def tau0891 : RatBall :=
  ⟨⟨-37/160, 43/160⟩, 3/320⟩
def center0891 : GaussianRat :=
  ⟨-84477561/500000000, 89929857/500000000⟩
def contact0891 : RatBall := localContactBall tau0891 center0891
def work0891 : RoundedTauEval :=
  evalTau precision tau0891 contact0891 logTwoBall

theorem center_sq0891 : (center0891.re : ℝ)^2 +
    (center0891.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0891]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0891 : work0891.theta.ok = true ∧
    work0891.jac.invOK = true ∧ acceptsUnitSq work0891.out = true := by decide +kernel

def cell0891 : CellCertificate where
  tauBall := tau0891
  contactCenter := center0891
  contactBall := contact0891
  work := work0891
  center_sq := center_sq0891
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0891.1
  jac_ok := checks0891.2.1
  accepted := checks0891.2.2

def tau0892 : RatBall :=
  ⟨⟨-7/32, 41/160⟩, 3/320⟩
def center0892 : GaussianRat :=
  ⟨-31833667/200000000, 43062577/250000000⟩
def contact0892 : RatBall := localContactBall tau0892 center0892
def work0892 : RoundedTauEval :=
  evalTau precision tau0892 contact0892 logTwoBall

theorem center_sq0892 : (center0892.re : ℝ)^2 +
    (center0892.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0892]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0892 : work0892.theta.ok = true ∧
    work0892.jac.invOK = true ∧ acceptsUnitSq work0892.out = true := by decide +kernel

def cell0892 : CellCertificate where
  tauBall := tau0892
  contactCenter := center0892
  contactBall := contact0892
  work := work0892
  center_sq := center_sq0892
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0892.1
  jac_ok := checks0892.2.1
  accepted := checks0892.2.2

def tau0893 : RatBall :=
  ⟨⟨-33/160, 41/160⟩, 3/320⟩
def center0893 : GaussianRat :=
  ⟨-150430267/1000000000, 1082879/6250000⟩
def contact0893 : RatBall := localContactBall tau0893 center0893
def work0893 : RoundedTauEval :=
  evalTau precision tau0893 contact0893 logTwoBall

theorem center_sq0893 : (center0893.re : ℝ)^2 +
    (center0893.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0893]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0893 : work0893.theta.ok = true ∧
    work0893.jac.invOK = true ∧ acceptsUnitSq work0893.out = true := by decide +kernel

def cell0893 : CellCertificate where
  tauBall := tau0893
  contactCenter := center0893
  contactBall := contact0893
  work := work0893
  center_sq := center_sq0893
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0893.1
  jac_ok := checks0893.2.1
  accepted := checks0893.2.2

def tau0894 : RatBall :=
  ⟨⟨-7/32, 43/160⟩, 3/320⟩
def center0894 : GaussianRat :=
  ⟨-160233593/1000000000, 180980837/1000000000⟩
def contact0894 : RatBall := localContactBall tau0894 center0894
def work0894 : RoundedTauEval :=
  evalTau precision tau0894 contact0894 logTwoBall

theorem center_sq0894 : (center0894.re : ℝ)^2 +
    (center0894.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0894]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0894 : work0894.theta.ok = true ∧
    work0894.jac.invOK = true ∧ acceptsUnitSq work0894.out = true := by decide +kernel

def cell0894 : CellCertificate where
  tauBall := tau0894
  contactCenter := center0894
  contactBall := contact0894
  work := work0894
  center_sq := center_sq0894
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0894.1
  jac_ok := checks0894.2.1
  accepted := checks0894.2.2

def tau0895 : RatBall :=
  ⟨⟨-33/160, 43/160⟩, 3/320⟩
def center0895 : GaussianRat :=
  ⟨-151447357/1000000000, 91026767/500000000⟩
def contact0895 : RatBall := localContactBall tau0895 center0895
def work0895 : RoundedTauEval :=
  evalTau precision tau0895 contact0895 logTwoBall

theorem center_sq0895 : (center0895.re : ℝ)^2 +
    (center0895.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0895]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0895 : work0895.theta.ok = true ∧
    work0895.jac.invOK = true ∧ acceptsUnitSq work0895.out = true := by decide +kernel

def cell0895 : CellCertificate where
  tauBall := tau0895
  contactCenter := center0895
  contactBall := contact0895
  work := work0895
  center_sq := center_sq0895
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0895.1
  jac_ok := checks0895.2.1
  accepted := checks0895.2.2

def cells : List CellCertificate := [cell0888, cell0889, cell0890, cell0891, cell0892, cell0893, cell0894, cell0895]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111

end


