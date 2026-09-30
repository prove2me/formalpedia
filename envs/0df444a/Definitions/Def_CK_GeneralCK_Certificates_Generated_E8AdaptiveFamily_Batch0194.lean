-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0194
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0194
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:38:26.148008+00:00
-- url     : https://prove2.me/theorems/46a181bc-0bb2-4c3b-b594-94dc5590b8e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0194.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1552 : RatBall :=
  ⟨⟨13/320, -121/320⟩, 3/640⟩
def center1552 : GaussianRat :=
  ⟨8256217/250000000, -34467723/125000000⟩
def contact1552 : RatBall := localContactBall tau1552 center1552
def work1552 : RoundedTauEval :=
  evalTau precision tau1552 contact1552 logTwoBall

theorem center_sq1552 : (center1552.re : ℝ)^2 +
    (center1552.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1552]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1552 : work1552.theta.ok = true ∧
    work1552.jac.invOK = true ∧ acceptsUnitSq work1552.out = true := by decide +kernel

def cell1552 : CellCertificate where
  tauBall := tau1552
  contactCenter := center1552
  contactBall := contact1552
  work := work1552
  center_sq := center_sq1552
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1552.1
  jac_ok := checks1552.2.1
  accepted := checks1552.2.2

def tau1553 : RatBall :=
  ⟨⟨3/64, -121/320⟩, 3/640⟩
def center1553 : GaussianRat :=
  ⟨38091451/1000000000, -137769289/500000000⟩
def contact1553 : RatBall := localContactBall tau1553 center1553
def work1553 : RoundedTauEval :=
  evalTau precision tau1553 contact1553 logTwoBall

theorem center_sq1553 : (center1553.re : ℝ)^2 +
    (center1553.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1553]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1553 : work1553.theta.ok = true ∧
    work1553.jac.invOK = true ∧ acceptsUnitSq work1553.out = true := by decide +kernel

def cell1553 : CellCertificate where
  tauBall := tau1553
  contactCenter := center1553
  contactBall := contact1553
  work := work1553
  center_sq := center_sq1553
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1553.1
  jac_ok := checks1553.2.1
  accepted := checks1553.2.2

def tau1554 : RatBall :=
  ⟨⟨1/320, -119/320⟩, 3/640⟩
def center1554 : GaussianRat :=
  ⟨1264407/500000000, -33910207/125000000⟩
def contact1554 : RatBall := localContactBall tau1554 center1554
def work1554 : RoundedTauEval :=
  evalTau precision tau1554 contact1554 logTwoBall

theorem center_sq1554 : (center1554.re : ℝ)^2 +
    (center1554.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1554]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1554 : work1554.theta.ok = true ∧
    work1554.jac.invOK = true ∧ acceptsUnitSq work1554.out = true := by decide +kernel

def cell1554 : CellCertificate where
  tauBall := tau1554
  contactCenter := center1554
  contactBall := contact1554
  work := work1554
  center_sq := center_sq1554
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1554.1
  jac_ok := checks1554.2.1
  accepted := checks1554.2.2

def tau1555 : RatBall :=
  ⟨⟨3/320, -119/320⟩, 3/640⟩
def center1555 : GaussianRat :=
  ⟨3793023/500000000, -135626627/500000000⟩
def contact1555 : RatBall := localContactBall tau1555 center1555
def work1555 : RoundedTauEval :=
  evalTau precision tau1555 contact1555 logTwoBall

theorem center_sq1555 : (center1555.re : ℝ)^2 +
    (center1555.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1555]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1555 : work1555.theta.ok = true ∧
    work1555.jac.invOK = true ∧ acceptsUnitSq work1555.out = true := by decide +kernel

def cell1555 : CellCertificate where
  tauBall := tau1555
  contactCenter := center1555
  contactBall := contact1555
  work := work1555
  center_sq := center_sq1555
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1555.1
  jac_ok := checks1555.2.1
  accepted := checks1555.2.2

def tau1556 : RatBall :=
  ⟨⟨1/320, -117/320⟩, 3/640⟩
def center1556 : GaussianRat :=
  ⟨314351/125000000, -66559541/250000000⟩
def contact1556 : RatBall := localContactBall tau1556 center1556
def work1556 : RoundedTauEval :=
  evalTau precision tau1556 contact1556 logTwoBall

theorem center_sq1556 : (center1556.re : ℝ)^2 +
    (center1556.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1556]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1556 : work1556.theta.ok = true ∧
    work1556.jac.invOK = true ∧ acceptsUnitSq work1556.out = true := by decide +kernel

def cell1556 : CellCertificate where
  tauBall := tau1556
  contactCenter := center1556
  contactBall := contact1556
  work := work1556
  center_sq := center_sq1556
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1556.1
  jac_ok := checks1556.2.1
  accepted := checks1556.2.2

def tau1557 : RatBall :=
  ⟨⟨3/320, -117/320⟩, 3/640⟩
def center1557 : GaussianRat :=
  ⟨7544037/1000000000, -16638159/62500000⟩
def contact1557 : RatBall := localContactBall tau1557 center1557
def work1557 : RoundedTauEval :=
  evalTau precision tau1557 contact1557 logTwoBall

theorem center_sq1557 : (center1557.re : ℝ)^2 +
    (center1557.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1557]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1557 : work1557.theta.ok = true ∧
    work1557.jac.invOK = true ∧ acceptsUnitSq work1557.out = true := by decide +kernel

def cell1557 : CellCertificate where
  tauBall := tau1557
  contactCenter := center1557
  contactBall := contact1557
  work := work1557
  center_sq := center_sq1557
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1557.1
  jac_ok := checks1557.2.1
  accepted := checks1557.2.2

def tau1558 : RatBall :=
  ⟨⟨1/64, -119/320⟩, 3/640⟩
def center1558 : GaussianRat :=
  ⟨1264209/100000000, -27119647/100000000⟩
def contact1558 : RatBall := localContactBall tau1558 center1558
def work1558 : RoundedTauEval :=
  evalTau precision tau1558 contact1558 logTwoBall

theorem center_sq1558 : (center1558.re : ℝ)^2 +
    (center1558.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1558]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1558 : work1558.theta.ok = true ∧
    work1558.jac.invOK = true ∧ acceptsUnitSq work1558.out = true := by decide +kernel

def cell1558 : CellCertificate where
  tauBall := tau1558
  contactCenter := center1558
  contactBall := contact1558
  work := work1558
  center_sq := center_sq1558
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1558.1
  jac_ok := checks1558.2.1
  accepted := checks1558.2.2

def tau1559 : RatBall :=
  ⟨⟨7/320, -119/320⟩, 3/640⟩
def center1559 : GaussianRat :=
  ⟨3539231/200000000, -67777837/250000000⟩
def contact1559 : RatBall := localContactBall tau1559 center1559
def work1559 : RoundedTauEval :=
  evalTau precision tau1559 contact1559 logTwoBall

theorem center_sq1559 : (center1559.re : ℝ)^2 +
    (center1559.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1559]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1559 : work1559.theta.ok = true ∧
    work1559.jac.invOK = true ∧ acceptsUnitSq work1559.out = true := by decide +kernel

def cell1559 : CellCertificate where
  tauBall := tau1559
  contactCenter := center1559
  contactBall := contact1559
  work := work1559
  center_sq := center_sq1559
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1559.1
  jac_ok := checks1559.2.1
  accepted := checks1559.2.2

def cells : List CellCertificate := [cell1552, cell1553, cell1554, cell1555, cell1556, cell1557, cell1558, cell1559]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194

end


