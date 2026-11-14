-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch08
-- name    : row23_rh_supp_RHLow100ThetaBatch08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:51:21.105433+00:00
-- url     : https://prove2.me/theorems/a6657b91-cb1b-4115-9965-b38fd6a484d5
-- title:
--   Row 23 RH support: RHLow100ThetaBatch08
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
theorem row08point0 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row08point1 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨1, by decide⟩) = true := by
  decide +kernel
theorem row08point2 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨2, by decide⟩) = true := by
  decide +kernel
theorem row08point3 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨3, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨3, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row08point4 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨4, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨4, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row08point5 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨5, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨5, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row08point6 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨6, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨6, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row08point7 (ha : CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨8, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨8, by decide⟩ ⟨7, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨8, by decide⟩ ⟨7, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
end RHLow100Theta
#print axioms RHLow100Theta.row08point0
#print axioms RHLow100Theta.row08point1
#print axioms RHLow100Theta.row08point2
#print axioms RHLow100Theta.row08point3
#print axioms RHLow100Theta.row08point4
#print axioms RHLow100Theta.row08point5
#print axioms RHLow100Theta.row08point6
#print axioms RHLow100Theta.row08point7


