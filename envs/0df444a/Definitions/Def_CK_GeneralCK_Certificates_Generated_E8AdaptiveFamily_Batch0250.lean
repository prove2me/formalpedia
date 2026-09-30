-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0250
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0250
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:30:03.663406+00:00
-- url     : https://prove2.me/theorems/5738bdc2-eca0-46c2-a0b7-51ee2353eebc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0250.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2000 : RatBall :=
  ⟨⟨-73/320, 101/320⟩, 3/640⟩
def center2000 : GaussianRat :=
  ⟨-85759271/500000000, 26642441/125000000⟩
def contact2000 : RatBall := localContactBall tau2000 center2000
def work2000 : RoundedTauEval :=
  evalTau precision tau2000 contact2000 logTwoBall

theorem center_sq2000 : (center2000.re : ℝ)^2 +
    (center2000.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2000 : work2000.theta.ok = true ∧
    work2000.jac.invOK = true ∧ acceptsUnitSq work2000.out = true := by decide +kernel

def cell2000 : CellCertificate where
  tauBall := tau2000
  contactCenter := center2000
  contactBall := contact2000
  work := work2000
  center_sq := center_sq2000
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2000.1
  jac_ok := checks2000.2.1
  accepted := checks2000.2.2

def tau2001 : RatBall :=
  ⟨⟨-15/64, 103/320⟩, 3/640⟩
def center2001 : GaussianRat :=
  ⟨-44170389/250000000, 43373931/200000000⟩
def contact2001 : RatBall := localContactBall tau2001 center2001
def work2001 : RoundedTauEval :=
  evalTau precision tau2001 contact2001 logTwoBall

theorem center_sq2001 : (center2001.re : ℝ)^2 +
    (center2001.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2001]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2001 : work2001.theta.ok = true ∧
    work2001.jac.invOK = true ∧ acceptsUnitSq work2001.out = true := by decide +kernel

def cell2001 : CellCertificate where
  tauBall := tau2001
  contactCenter := center2001
  contactBall := contact2001
  work := work2001
  center_sq := center_sq2001
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2001.1
  jac_ok := checks2001.2.1
  accepted := checks2001.2.2

def tau2002 : RatBall :=
  ⟨⟨-73/320, 103/320⟩, 3/640⟩
def center2002 : GaussianRat :=
  ⟨-34445579/200000000, 217595773/1000000000⟩
def contact2002 : RatBall := localContactBall tau2002 center2002
def work2002 : RoundedTauEval :=
  evalTau precision tau2002 contact2002 logTwoBall

theorem center_sq2002 : (center2002.re : ℝ)^2 +
    (center2002.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2002]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2002 : work2002.theta.ok = true ∧
    work2002.jac.invOK = true ∧ acceptsUnitSq work2002.out = true := by decide +kernel

def cell2002 : CellCertificate where
  tauBall := tau2002
  contactCenter := center2002
  contactBall := contact2002
  work := work2002
  center_sq := center_sq2002
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2002.1
  jac_ok := checks2002.2.1
  accepted := checks2002.2.2

def tau2003 : RatBall :=
  ⟨⟨-71/320, 97/320⟩, 3/640⟩
def center2003 : GaussianRat :=
  ⟨-41431439/250000000, 204924691/1000000000⟩
def contact2003 : RatBall := localContactBall tau2003 center2003
def work2003 : RoundedTauEval :=
  evalTau precision tau2003 contact2003 logTwoBall

theorem center_sq2003 : (center2003.re : ℝ)^2 +
    (center2003.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2003]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2003 : work2003.theta.ok = true ∧
    work2003.jac.invOK = true ∧ acceptsUnitSq work2003.out = true := by decide +kernel

def cell2003 : CellCertificate where
  tauBall := tau2003
  contactCenter := center2003
  contactBall := contact2003
  work := work2003
  center_sq := center_sq2003
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2003.1
  jac_ok := checks2003.2.1
  accepted := checks2003.2.2

def tau2004 : RatBall :=
  ⟨⟨-69/320, 97/320⟩, 3/640⟩
def center2004 : GaussianRat :=
  ⟨-161277047/1000000000, 51391661/250000000⟩
def contact2004 : RatBall := localContactBall tau2004 center2004
def work2004 : RoundedTauEval :=
  evalTau precision tau2004 contact2004 logTwoBall

theorem center_sq2004 : (center2004.re : ℝ)^2 +
    (center2004.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2004]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2004 : work2004.theta.ok = true ∧
    work2004.jac.invOK = true ∧ acceptsUnitSq work2004.out = true := by decide +kernel

def cell2004 : CellCertificate where
  tauBall := tau2004
  contactCenter := center2004
  contactBall := contact2004
  work := work2004
  center_sq := center_sq2004
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2004.1
  jac_ok := checks2004.2.1
  accepted := checks2004.2.2

def tau2005 : RatBall :=
  ⟨⟨-71/320, 99/320⟩, 3/640⟩
def center2005 : GaussianRat :=
  ⟨-83191847/500000000, 52342851/250000000⟩
def contact2005 : RatBall := localContactBall tau2005 center2005
def work2005 : RoundedTauEval :=
  evalTau precision tau2005 contact2005 logTwoBall

theorem center_sq2005 : (center2005.re : ℝ)^2 +
    (center2005.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2005]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2005 : work2005.theta.ok = true ∧
    work2005.jac.invOK = true ∧ acceptsUnitSq work2005.out = true := by decide +kernel

def cell2005 : CellCertificate where
  tauBall := tau2005
  contactCenter := center2005
  contactBall := contact2005
  work := work2005
  center_sq := center_sq2005
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2005.1
  jac_ok := checks2005.2.1
  accepted := checks2005.2.2

def tau2006 : RatBall :=
  ⟨⟨-69/320, 99/320⟩, 3/640⟩
def center2006 : GaussianRat :=
  ⟨-161920883/1000000000, 210031337/1000000000⟩
def contact2006 : RatBall := localContactBall tau2006 center2006
def work2006 : RoundedTauEval :=
  evalTau precision tau2006 contact2006 logTwoBall

theorem center_sq2006 : (center2006.re : ℝ)^2 +
    (center2006.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2006]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2006 : work2006.theta.ok = true ∧
    work2006.jac.invOK = true ∧ acceptsUnitSq work2006.out = true := by decide +kernel

def cell2006 : CellCertificate where
  tauBall := tau2006
  contactCenter := center2006
  contactBall := contact2006
  work := work2006
  center_sq := center_sq2006
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2006.1
  jac_ok := checks2006.2.1
  accepted := checks2006.2.2

def tau2007 : RatBall :=
  ⟨⟨-67/320, 97/320⟩, 3/640⟩
def center2007 : GaussianRat :=
  ⟨-19601337/125000000, 103097251/500000000⟩
def contact2007 : RatBall := localContactBall tau2007 center2007
def work2007 : RoundedTauEval :=
  evalTau precision tau2007 contact2007 logTwoBall

theorem center_sq2007 : (center2007.re : ℝ)^2 +
    (center2007.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2007]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2007 : work2007.theta.ok = true ∧
    work2007.jac.invOK = true ∧ acceptsUnitSq work2007.out = true := by decide +kernel

def cell2007 : CellCertificate where
  tauBall := tau2007
  contactCenter := center2007
  contactBall := contact2007
  work := work2007
  center_sq := center_sq2007
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2007.1
  jac_ok := checks2007.2.1
  accepted := checks2007.2.2

def cells : List CellCertificate := [cell2000, cell2001, cell2002, cell2003, cell2004, cell2005, cell2006, cell2007]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250

end


