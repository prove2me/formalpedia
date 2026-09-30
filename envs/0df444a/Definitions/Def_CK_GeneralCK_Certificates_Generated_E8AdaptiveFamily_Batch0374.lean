-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0374
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0374
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:32:09.207616+00:00
-- url     : https://prove2.me/theorems/3b1faecd-91ca-4652-8da7-81d0bf63b681
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0374.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2992 : RatBall :=
  ⟨⟨43/640, -247/640⟩, 3/1280⟩
def center2992 : GaussianRat :=
  ⟨3431607/62500000, -70250913/250000000⟩
def contact2992 : RatBall := localContactBall tau2992 center2992
def work2992 : RoundedTauEval :=
  evalTau precision tau2992 contact2992 logTwoBall

theorem center_sq2992 : (center2992.re : ℝ)^2 +
    (center2992.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2992]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2992 : work2992.theta.ok = true ∧
    work2992.jac.invOK = true ∧ acceptsUnitSq work2992.out = true := by decide +kernel

def cell2992 : CellCertificate where
  tauBall := tau2992
  contactCenter := center2992
  contactBall := contact2992
  work := work2992
  center_sq := center_sq2992
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2992.1
  jac_ok := checks2992.2.1
  accepted := checks2992.2.2

def tau2993 : RatBall :=
  ⟨⟨41/640, -49/128⟩, 3/1280⟩
def center2993 : GaussianRat :=
  ⟨13053747/250000000, -34827989/125000000⟩
def contact2993 : RatBall := localContactBall tau2993 center2993
def work2993 : RoundedTauEval :=
  evalTau precision tau2993 contact2993 logTwoBall

theorem center_sq2993 : (center2993.re : ℝ)^2 +
    (center2993.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2993]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2993 : work2993.theta.ok = true ∧
    work2993.jac.invOK = true ∧ acceptsUnitSq work2993.out = true := by decide +kernel

def cell2993 : CellCertificate where
  tauBall := tau2993
  contactCenter := center2993
  contactBall := contact2993
  work := work2993
  center_sq := center_sq2993
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2993.1
  jac_ok := checks2993.2.1
  accepted := checks2993.2.2

def tau2994 : RatBall :=
  ⟨⟨43/640, -49/128⟩, 3/1280⟩
def center2994 : GaussianRat :=
  ⟨6843329/125000000, -556939/2000000⟩
def contact2994 : RatBall := localContactBall tau2994 center2994
def work2994 : RoundedTauEval :=
  evalTau precision tau2994 contact2994 logTwoBall

theorem center_sq2994 : (center2994.re : ℝ)^2 +
    (center2994.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2994]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2994 : work2994.theta.ok = true ∧
    work2994.jac.invOK = true ∧ acceptsUnitSq work2994.out = true := by decide +kernel

def cell2994 : CellCertificate where
  tauBall := tau2994
  contactCenter := center2994
  contactBall := contact2994
  work := work2994
  center_sq := center_sq2994
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2994.1
  jac_ok := checks2994.2.1
  accepted := checks2994.2.2

def tau2995 : RatBall :=
  ⟨⟨9/128, -247/640⟩, 3/1280⟩
def center2995 : GaussianRat :=
  ⟨2872117/50000000, -14041993/50000000⟩
def contact2995 : RatBall := localContactBall tau2995 center2995
def work2995 : RoundedTauEval :=
  evalTau precision tau2995 contact2995 logTwoBall

theorem center_sq2995 : (center2995.re : ℝ)^2 +
    (center2995.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2995]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2995 : work2995.theta.ok = true ∧
    work2995.jac.invOK = true ∧ acceptsUnitSq work2995.out = true := by decide +kernel

def cell2995 : CellCertificate where
  tauBall := tau2995
  contactCenter := center2995
  contactBall := contact2995
  work := work2995
  center_sq := center_sq2995
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2995.1
  jac_ok := checks2995.2.1
  accepted := checks2995.2.2

def tau2996 : RatBall :=
  ⟨⟨47/640, -247/640⟩, 3/1280⟩
def center2996 : GaussianRat :=
  ⟨59976659/1000000000, -70167217/250000000⟩
def contact2996 : RatBall := localContactBall tau2996 center2996
def work2996 : RoundedTauEval :=
  evalTau precision tau2996 contact2996 logTwoBall

theorem center_sq2996 : (center2996.re : ℝ)^2 +
    (center2996.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2996]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2996 : work2996.theta.ok = true ∧
    work2996.jac.invOK = true ∧ acceptsUnitSq work2996.out = true := by decide +kernel

def cell2996 : CellCertificate where
  tauBall := tau2996
  contactCenter := center2996
  contactBall := contact2996
  work := work2996
  center_sq := center_sq2996
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2996.1
  jac_ok := checks2996.2.1
  accepted := checks2996.2.2

def tau2997 : RatBall :=
  ⟨⟨9/128, -49/128⟩, 3/1280⟩
def center2997 : GaussianRat :=
  ⟨57276093/1000000000, -139153977/500000000⟩
def contact2997 : RatBall := localContactBall tau2997 center2997
def work2997 : RoundedTauEval :=
  evalTau precision tau2997 contact2997 logTwoBall

theorem center_sq2997 : (center2997.re : ℝ)^2 +
    (center2997.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2997]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2997 : work2997.theta.ok = true ∧
    work2997.jac.invOK = true ∧ acceptsUnitSq work2997.out = true := by decide +kernel

def cell2997 : CellCertificate where
  tauBall := tau2997
  contactCenter := center2997
  contactBall := contact2997
  work := work2997
  center_sq := center_sq2997
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2997.1
  jac_ok := checks2997.2.1
  accepted := checks2997.2.2

def tau2998 : RatBall :=
  ⟨⟨47/640, -49/128⟩, 3/1280⟩
def center2998 : GaussianRat :=
  ⟨2392131/40000000, -55627861/200000000⟩
def contact2998 : RatBall := localContactBall tau2998 center2998
def work2998 : RoundedTauEval :=
  evalTau precision tau2998 contact2998 logTwoBall

theorem center_sq2998 : (center2998.re : ℝ)^2 +
    (center2998.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2998]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2998 : work2998.theta.ok = true ∧
    work2998.jac.invOK = true ∧ acceptsUnitSq work2998.out = true := by decide +kernel

def cell2998 : CellCertificate where
  tauBall := tau2998
  contactCenter := center2998
  contactBall := contact2998
  work := work2998
  center_sq := center_sq2998
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2998.1
  jac_ok := checks2998.2.1
  accepted := checks2998.2.2

def tau2999 : RatBall :=
  ⟨⟨9/128, -243/640⟩, 3/1280⟩
def center2999 : GaussianRat :=
  ⟨456897/8000000, -17236447/62500000⟩
def contact2999 : RatBall := localContactBall tau2999 center2999
def work2999 : RoundedTauEval :=
  evalTau precision tau2999 contact2999 logTwoBall

theorem center_sq2999 : (center2999.re : ℝ)^2 +
    (center2999.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2999]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2999 : work2999.theta.ok = true ∧
    work2999.jac.invOK = true ∧ acceptsUnitSq work2999.out = true := by decide +kernel

def cell2999 : CellCertificate where
  tauBall := tau2999
  contactCenter := center2999
  contactBall := contact2999
  work := work2999
  center_sq := center_sq2999
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2999.1
  jac_ok := checks2999.2.1
  accepted := checks2999.2.2

def cells : List CellCertificate := [cell2992, cell2993, cell2994, cell2995, cell2996, cell2997, cell2998, cell2999]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374

end


