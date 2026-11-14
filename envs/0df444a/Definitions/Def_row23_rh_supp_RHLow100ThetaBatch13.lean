-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch13
-- name    : row23_rh_supp_RHLow100ThetaBatch13
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:51:30.278663+00:00
-- url     : https://prove2.me/theorems/476f620b-80aa-42fd-820a-913f3e3eac43
-- title:
--   Row 23 RH support: RHLow100ThetaBatch13
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_TaoFivePrimes_RH14To100ThetaInterface
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace RHLow100Theta
theorem row13point0 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row13point1 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨1, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨1, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row13point2 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨2, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨2, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row13point3 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨3, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨3, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row13point4 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨4, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨4, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row13point5 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨5, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨5, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row13point6 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨6, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨6, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row13point7 (ha : CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨13, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨13, by decide⟩ ⟨7, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨13, by decide⟩ ⟨7, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
end RHLow100Theta
#print axioms RHLow100Theta.row13point0
#print axioms RHLow100Theta.row13point1
#print axioms RHLow100Theta.row13point2
#print axioms RHLow100Theta.row13point3
#print axioms RHLow100Theta.row13point4
#print axioms RHLow100Theta.row13point5
#print axioms RHLow100Theta.row13point6
#print axioms RHLow100Theta.row13point7


