-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0192
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0192
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:34:25.877115+00:00
-- url     : https://prove2.me/theorems/6c745c4a-21c5-4793-973c-28aae53423fd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0192.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1536 : RatBall :=
  ⟨⟨-23/320, -111/320⟩, 3/640⟩
def center1536 : GaussianRat :=
  ⟨-11349381/200000000, -62401781/250000000⟩
def contact1536 : RatBall := localContactBall tau1536 center1536
def work1536 : RoundedTauEval :=
  evalTau precision tau1536 contact1536 logTwoBall

theorem center_sq1536 : (center1536.re : ℝ)^2 +
    (center1536.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1536]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1536 : work1536.theta.ok = true ∧
    work1536.jac.invOK = true ∧ acceptsUnitSq work1536.out = true := by decide +kernel

def cell1536 : CellCertificate where
  tauBall := tau1536
  contactCenter := center1536
  contactBall := contact1536
  work := work1536
  center_sq := center_sq1536
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1536.1
  jac_ok := checks1536.2.1
  accepted := checks1536.2.2

def tau1537 : RatBall :=
  ⟨⟨-21/320, -111/320⟩, 3/640⟩
def center1537 : GaussianRat :=
  ⟨-51839561/1000000000, -31235321/125000000⟩
def contact1537 : RatBall := localContactBall tau1537 center1537
def work1537 : RoundedTauEval :=
  evalTau precision tau1537 contact1537 logTwoBall

theorem center_sq1537 : (center1537.re : ℝ)^2 +
    (center1537.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1537]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1537 : work1537.theta.ok = true ∧
    work1537.jac.invOK = true ∧ acceptsUnitSq work1537.out = true := by decide +kernel

def cell1537 : CellCertificate where
  tauBall := tau1537
  contactCenter := center1537
  contactBall := contact1537
  work := work1537
  center_sq := center_sq1537
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1537.1
  jac_ok := checks1537.2.1
  accepted := checks1537.2.2

def tau1538 : RatBall :=
  ⟨⟨-23/320, -109/320⟩, 3/640⟩
def center1538 : GaussianRat :=
  ⟨-56463291/1000000000, -15294731/62500000⟩
def contact1538 : RatBall := localContactBall tau1538 center1538
def work1538 : RoundedTauEval :=
  evalTau precision tau1538 contact1538 logTwoBall

theorem center_sq1538 : (center1538.re : ℝ)^2 +
    (center1538.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1538]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1538 : work1538.theta.ok = true ∧
    work1538.jac.invOK = true ∧ acceptsUnitSq work1538.out = true := by decide +kernel

def cell1538 : CellCertificate where
  tauBall := tau1538
  contactCenter := center1538
  contactBall := contact1538
  work := work1538
  center_sq := center_sq1538
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1538.1
  jac_ok := checks1538.2.1
  accepted := checks1538.2.2

def tau1539 : RatBall :=
  ⟨⟨-21/320, -109/320⟩, 3/640⟩
def center1539 : GaussianRat :=
  ⟨-51579953/1000000000, -48996707/200000000⟩
def contact1539 : RatBall := localContactBall tau1539 center1539
def work1539 : RoundedTauEval :=
  evalTau precision tau1539 contact1539 logTwoBall

theorem center_sq1539 : (center1539.re : ℝ)^2 +
    (center1539.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1539]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1539 : work1539.theta.ok = true ∧
    work1539.jac.invOK = true ∧ acceptsUnitSq work1539.out = true := by decide +kernel

def cell1539 : CellCertificate where
  tauBall := tau1539
  contactCenter := center1539
  contactBall := contact1539
  work := work1539
  center_sq := center_sq1539
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1539.1
  jac_ok := checks1539.2.1
  accepted := checks1539.2.2

def tau1540 : RatBall :=
  ⟨⟨-113/320, -61/320⟩, 3/640⟩
def center1540 : GaussianRat :=
  ⟨-242396513/1000000000, -117649273/1000000000⟩
def contact1540 : RatBall := localContactBall tau1540 center1540
def work1540 : RoundedTauEval :=
  evalTau precision tau1540 contact1540 logTwoBall

theorem center_sq1540 : (center1540.re : ℝ)^2 +
    (center1540.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1540]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1540 : work1540.theta.ok = true ∧
    work1540.jac.invOK = true ∧ acceptsUnitSq work1540.out = true := by decide +kernel

def cell1540 : CellCertificate where
  tauBall := tau1540
  contactCenter := center1540
  contactBall := contact1540
  work := work1540
  center_sq := center_sq1540
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1540.1
  jac_ok := checks1540.2.1
  accepted := checks1540.2.2

def tau1541 : RatBall :=
  ⟨⟨1/320, -123/320⟩, 3/640⟩
def center1541 : GaussianRat :=
  ⟨2558027/1000000000, -14072733/50000000⟩
def contact1541 : RatBall := localContactBall tau1541 center1541
def work1541 : RoundedTauEval :=
  evalTau precision tau1541 contact1541 logTwoBall

theorem center_sq1541 : (center1541.re : ℝ)^2 +
    (center1541.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1541]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1541 : work1541.theta.ok = true ∧
    work1541.jac.invOK = true ∧ acceptsUnitSq work1541.out = true := by decide +kernel

def cell1541 : CellCertificate where
  tauBall := tau1541
  contactCenter := center1541
  contactBall := contact1541
  work := work1541
  center_sq := center_sq1541
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1541.1
  jac_ok := checks1541.2.1
  accepted := checks1541.2.2

def tau1542 : RatBall :=
  ⟨⟨3/320, -123/320⟩, 3/640⟩
def center1542 : GaussianRat :=
  ⟨3836831/500000000, -281424629/1000000000⟩
def contact1542 : RatBall := localContactBall tau1542 center1542
def work1542 : RoundedTauEval :=
  evalTau precision tau1542 contact1542 logTwoBall

theorem center_sq1542 : (center1542.re : ℝ)^2 +
    (center1542.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1542]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1542 : work1542.theta.ok = true ∧
    work1542.jac.invOK = true ∧ acceptsUnitSq work1542.out = true := by decide +kernel

def cell1542 : CellCertificate where
  tauBall := tau1542
  contactCenter := center1542
  contactBall := contact1542
  work := work1542
  center_sq := center_sq1542
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1542.1
  jac_ok := checks1542.2.1
  accepted := checks1542.2.2

def tau1543 : RatBall :=
  ⟨⟨1/320, -121/320⟩, 3/640⟩
def center1543 : GaussianRat :=
  ⟨2543217/1000000000, -276353553/1000000000⟩
def contact1543 : RatBall := localContactBall tau1543 center1543
def work1543 : RoundedTauEval :=
  evalTau precision tau1543 contact1543 logTwoBall

theorem center_sq1543 : (center1543.re : ℝ)^2 +
    (center1543.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1543]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1543 : work1543.theta.ok = true ∧
    work1543.jac.invOK = true ∧ acceptsUnitSq work1543.out = true := by decide +kernel

def cell1543 : CellCertificate where
  tauBall := tau1543
  contactCenter := center1543
  contactBall := contact1543
  work := work1543
  center_sq := center_sq1543
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1543.1
  jac_ok := checks1543.2.1
  accepted := checks1543.2.2

def cells : List CellCertificate := [cell1536, cell1537, cell1538, cell1539, cell1540, cell1541, cell1542, cell1543]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192

end


